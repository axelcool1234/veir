module

public import Veir.Analysis.DataFlow.Domains.ConstantDomain
public import Veir.Analysis.DataFlow.SparseAnalysis

public section

namespace Veir

namespace SparseConstantPropagation

-- The whole analysis is declared in one place: the `.sparseConstant` fact slot
-- stores `AbstractConstant` values, and the analysis is scheduled under the
-- `.sparseConstantPropagation` tag. `FactPayload .sparseConstant` is
-- definitionally `SparsePayload AbstractConstant`, so the payload iso is the
-- identity and its round-trip laws hold by `rfl`.
instance : SparseForwardSpec .sparseConstant AbstractConstant where
  toPayload := id
  ofPayload := id
  of_to _ := rfl
  to_of _ := rfl
  analysisKind := .sparseConstantPropagation

/--
Fold a binary operation on known constants when bitwidths agree.
Returns `none` if widths mismatch or folding yields no value.
-/
def foldKnownBinary?
    (lhs rhs : ConcreteConstant)
    (f : {w : Nat} -> Data.LLVM.Int w -> Data.LLVM.Int w -> Option (Data.LLVM.Int w))
    : Option ConcreteConstant :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsValue := Data.LLVM.Int.cast rhs.value (Eq.symm h)
    f lhs.value rhsValue |> .map ({ bitwidth := lhs.bitwidth, value := · })
  else
    none

/--
Try to fold a binary op from its two operand abstractions.
Only folds when there are exactly two operands and both are known constants.
The framework guarantees these abstractions are never `⊥` (uninitialized).
-/
def foldBinary?
    (operandAbstractions : Array AbstractConstant)
    (f : {w : Nat} -> Data.LLVM.Int w -> Data.LLVM.Int w -> Option (Data.LLVM.Int w))
    : Option AbstractConstant :=
  if operandAbstractions.size ≠ 2 then
    none
  else
    match operandAbstractions[0]?, operandAbstractions[1]? with
    | some (AbstractConstant.constant lhs), some (AbstractConstant.constant rhs) =>
      foldKnownBinary? lhs rhs f |> .map (.constant ·)
    | _, _ => none

/--
Wrap the optional result of folding a single-result op: the folded constant when
folding succeeded, or the pessimistic `⊤` for every result otherwise.
-/
def foldedOrTop (numResults : Nat) (folded : Option AbstractConstant) : Array AbstractConstant :=
  match folded with
  | some constant => #[constant]
  | none => Array.replicate numResults ⊤

/--
Sparse constant propagation transfer function, as a pure map from operand
abstractions to result abstractions:
- region operations conservatively force results to the pessimistic state,
- otherwise we try to fold and report any discovered constant, falling back to
  `⊤` when folding is not possible.

The framework calls this only once every operand abstraction is initialized, and
is responsible for joining the returned abstractions back into the lattice.
-/
def transfer
    (op : OperationPtr)
    (irCtx : IRContext OpCode)
    (operandAbstractions : Array AbstractConstant) : Array AbstractConstant :=
  let numResults := op.getNumResults! irCtx

  -- Don't try to simulate the results of a region operation as we can't
  -- guarantee that folding will be out-of-place. We don't allow in-place
  -- folds as the desire here is for simulated execution, and not general
  -- folding.
  if op.getNumRegions! irCtx ≠ 0 then
    Array.replicate numResults ⊤
  else
    -- TODO: Mirror MLIR's generic `op->fold` path once Veir has an operation
    -- folder and fold-result representation. For now we manually handle the
    -- arithmetic ops.
    match (op.get! irCtx).opType with
    | .arith .constant =>
      -- Read the `arith.constant` and convert it into the lattice domain.
      let intAttr := (op.getProperties! irCtx (.arith .constant)).value
      #[.constant ⟨intAttr.type.bitwidth, Data.LLVM.Int.constant intAttr.type.bitwidth intAttr.value⟩]
    | .arith .addi =>
      let flags := op.getProperties! irCtx (.arith .addi)
      foldedOrTop numResults <| foldBinary? operandAbstractions (fun lhs rhs =>
        match Data.LLVM.Int.add lhs rhs flags.attr.nsw flags.attr.nuw with
        | .val v => some (.val v)
        | .poison => none)
    | .arith .muli =>
      let flags := op.getProperties! irCtx (.arith .muli)
      foldedOrTop numResults <| foldBinary? operandAbstractions (fun lhs rhs =>
        match Data.LLVM.Int.mul lhs rhs flags.attr.nsw flags.attr.nuw with
        | .val v => some (.val v)
        | .poison => none)
    | .arith .andi =>
      foldedOrTop numResults <| foldBinary? operandAbstractions (fun lhs rhs =>
        match lhs, rhs with
        | .val lhs', .val rhs' => some (.val (BitVec.and lhs' rhs'))
        | _, _ => none)
    | .arith .subi =>
      let flags := op.getProperties! irCtx (.arith .subi)
      foldedOrTop numResults <| foldBinary? operandAbstractions (fun lhs rhs =>
        match Data.LLVM.Int.sub lhs rhs flags.attr.nsw flags.attr.nuw with
        | .val v => some (.val v)
        | .poison => none)
    | _ =>
      Array.replicate numResults ⊤

/-! ## Monotonicity of the transfer function

`transfer` is monotone on `⊥`-free operands (see `Soundness.lean` for why the
`⊥`-freeness is essential). `ArrayLe` is the positional order on result arrays;
it is deliberately *not* length-indexed, because a successful fold yields a
length-1 array while a failed fold yields a length-`numResults` array, and the
positional order is exactly what the driver needs (it joins result-by-result). -/

/-- Positional order on result-abstraction arrays. -/
def ArrayLe (xs ys : Array AbstractConstant) : Prop :=
  ∀ (i : Nat) (a b : AbstractConstant), xs[i]? = some a → ys[i]? = some b → a ≤ b

theorem ArrayLe.refl (xs : Array AbstractConstant) : ArrayLe xs xs := by
  intro i a b ha hb
  rw [ha] at hb
  simp only [Option.some.injEq] at hb
  subst hb
  exact AbstractConstant.le_refl a

theorem ArrayLe.replicate_top (xs : Array AbstractConstant) (n : Nat) :
    ArrayLe xs (Array.replicate n ⊤) := by
  intro i a b ha hb
  simp only [Array.getElem?_replicate] at hb
  split at hb
  · simp only [Option.some.injEq] at hb
    subst hb
    exact AbstractConstant.le_top a
  · simp at hb

/-- If the (larger) operands `ys` fold to a constant, the (smaller, `⊥`-free)
operands `xs` fold to the *same* constant. -/
theorem foldBinary?_eq_of_ys {xs ys : Array AbstractConstant}
    (f : {w : Nat} → Data.LLVM.Int w → Data.LLVM.Int w → Option (Data.LLVM.Int w))
    (k : AbstractConstant)
    (hsize : xs.size = ys.size)
    (hxbot : ∀ (i : Nat) (a : AbstractConstant), xs[i]? = some a → a ≠ ⊥)
    (hle : ArrayLe xs ys)
    (hoy : foldBinary? ys f = some k) :
    foldBinary? xs f = some k := by
  unfold foldBinary? at hoy ⊢
  split at hoy
  · simp at hoy
  · next hys =>
    have hxs2 : ¬ xs.size ≠ 2 := by omega
    rw [if_neg hxs2]
    split at hoy
    · next lhs rhs hys0 hys1 =>
      have hx0 : xs[0]? = some (.constant lhs) := by
        cases hx0' : xs[0]? with
        | none => rw [Array.getElem?_eq_none_iff] at hx0'; omega
        | some a =>
          rw [AbstractConstant.eq_constant_of_le a lhs (hle 0 a _ hx0' hys0) (hxbot 0 a hx0')]
      have hx1 : xs[1]? = some (.constant rhs) := by
        cases hx1' : xs[1]? with
        | none => rw [Array.getElem?_eq_none_iff] at hx1'; omega
        | some a =>
          rw [AbstractConstant.eq_constant_of_le a rhs (hle 1 a _ hx1' hys1) (hxbot 1 a hx1')]
      rw [hx0, hx1]
      exact hoy
    · simp at hoy

theorem foldedOrTop_mono {xs ys : Array AbstractConstant} (n : Nat)
    (f : {w : Nat} → Data.LLVM.Int w → Data.LLVM.Int w → Option (Data.LLVM.Int w))
    (hsize : xs.size = ys.size)
    (hxbot : ∀ (i : Nat) (a : AbstractConstant), xs[i]? = some a → a ≠ ⊥)
    (hle : ArrayLe xs ys) :
    ArrayLe (foldedOrTop n (foldBinary? xs f)) (foldedOrTop n (foldBinary? ys f)) := by
  unfold foldedOrTop
  cases hoy : foldBinary? ys f with
  | none => exact ArrayLe.replicate_top _ n
  | some k =>
    have hox : foldBinary? xs f = some k := foldBinary?_eq_of_ys f k hsize hxbot hle hoy
    cases hox' : foldBinary? xs f with
    | none => rw [hox'] at hox; simp at hox
    | some k' =>
      rw [hox'] at hox
      simp only [Option.some.injEq] at hox
      subst hox
      exact ArrayLe.refl _

/--
`transfer` is monotone on `⊥`-free, equal-arity operands: raising the operands
can only raise the result abstractions (positionally). The `⊥`-freeness is
essential (the driver's wait-on-`⊥` guard provides it); see `Soundness.lean`.
-/
theorem transfer_monotone
    (op : OperationPtr) (irCtx : IRContext OpCode)
    (xs ys : Array AbstractConstant)
    (hsize : xs.size = ys.size)
    (hxbot : ∀ (i : Nat) (a : AbstractConstant), xs[i]? = some a → a ≠ ⊥)
    (hle : ArrayLe xs ys) :
    ArrayLe (transfer op irCtx xs) (transfer op irCtx ys) := by
  unfold transfer
  split
  · exact ArrayLe.replicate_top _ _
  · split
    all_goals first
      | exact ArrayLe.replicate_top _ _
      | exact ArrayLe.refl _
      | exact foldedOrTop_mono _ _ hsize hxbot hle

/--
When `foldBinary?` folds two known constants of the same bitwidth to a result, that
result is exactly the constant `f` computes on their values. This is the bridge
between the abstract fold and a concrete binary operation: pair it with a fold `f`
that mirrors the interpreter's op to get per-op soundness (see
`ConstantSoundness.lean`).
-/
theorem foldBinary?_eq (bw : Nat) (lv rv : Data.LLVM.Int bw)
    (f : {w : Nat} → Data.LLVM.Int w → Data.LLVM.Int w → Option (Data.LLVM.Int w))
    (res : AbstractConstant)
    (h : foldBinary? #[.constant ⟨bw, lv⟩, .constant ⟨bw, rv⟩] f = some res) :
    ∃ v, f lv rv = some v ∧ res = .constant ⟨bw, v⟩ := by
  simp [foldBinary?, foldKnownBinary?, Data.LLVM.Int.cast_self] at h
  obtain ⟨v, hv, hres⟩ := h
  exact ⟨v, hv, hres.symm⟩

end SparseConstantPropagation

def SparseConstantPropagationAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .sparseConstant
    SparseConstantPropagation.transfer

end Veir
