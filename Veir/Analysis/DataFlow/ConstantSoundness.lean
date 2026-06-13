import Veir.Analysis.DataFlow.Domains.ConstantDomain
import Veir.Analysis.DataFlow.MonotoneFramework
import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis
import Veir.Interpreter.Basic

namespace Veir

/-!
# The constant domain, concretized to interpreter runtime values

`AbstractDomain AbstractConstant ConcreteConstant` (in `ConstantDomain.lean`) gives
the order-theoretic content of constant propagation. To make the soundness
machinery (`MonotoneFramework.postfixpoint_sound` / `solve_sound`) bite against the
*actual* semantics, we need a concretization to the values the interpreter
manipulates — `RuntimeValue` — not the abstract `ConcreteConstant`.

This file provides exactly that bridge: `AbstractConstant.γRuntime` and an
`AbstractDomain AbstractConstant RuntimeValue` instance reusing the existing
lattice. With it, `solve_sound`/`postfixpoint_sound` can be instantiated at
`Concrete := RuntimeValue`, leaving only the per-operation transfer-soundness
obligations (e.g. `γRuntime_constant` below for `arith.constant`).
-/

namespace AbstractConstant

/-- Concretization of constant-domain abstractions to interpreter runtime values:
`⊤` denotes everything, `⊥` nothing, and `constant ⟨bw, v⟩` the single integer
runtime value `.int bw v`. -/
def γRuntime : AbstractConstant → Set RuntimeValue
  | .top => fun _ => True
  | .bottom => fun _ => False
  | .constant c => fun rv => rv = .int c.bitwidth c.value

theorem γRuntime_monotone (a b : AbstractConstant) : a ≤ b → γRuntime a ⊆ γRuntime b := by
  intro hab x hx
  cases a <;> cases b <;> simp [γRuntime, le_def, le] at hab hx ⊢
  all_goals first | trivial | exact hab ▸ hx

/-- An `int` runtime value concretizes only `⊤` or the matching constant. -/
theorem γRuntime_int_mem {bw : Nat} {lv : Data.LLVM.Int bw} {ac : AbstractConstant}
    (h : (.int bw lv : RuntimeValue) ∈ γRuntime ac) :
    ac = .top ∨ ac = .constant ⟨bw, lv⟩ := by
  cases ac with
  | top => exact Or.inl rfl
  | bottom => exact (show False from h).elim
  | constant c =>
    refine Or.inr ?_
    obtain ⟨cbw, cv⟩ := c
    replace h : (.int bw lv : RuntimeValue) = .int cbw cv := h
    injection h with hbw hlv
    subst hbw
    cases eq_of_heq hlv
    rfl

/-- The constant domain concretized to runtime values: the same lattice as
`AbstractDomain AbstractConstant ConcreteConstant`, but denoting interpreter
`RuntimeValue`s. -/
instance : AbstractDomain AbstractConstant RuntimeValue where
  toJoinSemilattice := inferInstance
  toBoundedOrder := inferInstance
  γ := γRuntime
  γ_top := rfl
  γ_bot := rfl
  γ_monotone := γRuntime_monotone

/--
The constant-propagation abstraction of an `arith.constant` concretizes the value
the interpreter computes for it. `SparseConstantPropagation.transfer` produces
`constant ⟨bw, Data.LLVM.Int.constant bw v⟩` and `Arith.interpretOp'` produces
`.int bw (.val (BitVec.ofInt bw v))`; both are `BitVec.ofInt`, so the runtime value
lies in the abstraction's concretization. This is the per-op soundness fact for the
constant case — the first instantiation of the bridge.
-/
theorem γRuntime_constant (bw : Nat) (v : _root_.Int) :
    (.int bw (.val (BitVec.ofInt bw v)) : RuntimeValue)
      ∈ γRuntime (.constant ⟨bw, Data.LLVM.Int.constant bw v⟩) := by
  show (.int bw (.val (BitVec.ofInt bw v)) : RuntimeValue)
    = .int bw (Data.LLVM.Int.constant bw v)
  rw [Data.LLVM.Int.constant]

/--
Soundness of a binary fold against a concrete result. If the SCCP fold `f` agrees
with the concrete binary result `g` whenever it succeeds (`hfg`), then the runtime
value `.int bw g` lies in the concretization of the abstraction the transfer
produces for that binary op (`foldBinary?`, defaulting to `⊤` when folding fails).
This is the reusable per-op soundness core for every `arith` binary op. -/
theorem foldBinary?_γRuntime_sound (bw : Nat) (lv rv : Data.LLVM.Int bw)
    (f : {w : Nat} → Data.LLVM.Int w → Data.LLVM.Int w → Option (Data.LLVM.Int w))
    (g : Data.LLVM.Int bw) (hfg : ∀ v, f lv rv = some v → v = g) :
    (.int bw g : RuntimeValue) ∈
      γRuntime ((SparseConstantPropagation.foldBinary?
        #[.constant ⟨bw, lv⟩, .constant ⟨bw, rv⟩] f).getD ⊤) := by
  cases hfb : SparseConstantPropagation.foldBinary?
      #[.constant ⟨bw, lv⟩, .constant ⟨bw, rv⟩] f with
  | none => exact trivial
  | some res =>
    obtain ⟨v, hv, hres⟩ := SparseConstantPropagation.foldBinary?_eq bw lv rv f res hfb
    subst hres
    show (.int bw g : RuntimeValue) = .int bw v
    rw [hfg v hv]

/--
`arith.addi` is sound: the runtime value the interpreter computes for an addition,
`.int bw (LLVM.Int.add lv rv nsw nuw)`, lies in the concretization of the
abstraction `SparseConstantPropagation.transfer` produces (its `addi` fold mirrors
`LLVM.Int.add`). The template applies verbatim to `muli`/`subi`/`andi`. -/
theorem addi_γRuntime_sound (bw : Nat) (lv rv : Data.LLVM.Int bw) (nsw nuw : Bool) :
    (.int bw (Data.LLVM.Int.add lv rv nsw nuw) : RuntimeValue) ∈
      γRuntime ((SparseConstantPropagation.foldBinary?
        #[.constant ⟨bw, lv⟩, .constant ⟨bw, rv⟩]
        (fun lhs rhs => match Data.LLVM.Int.add lhs rhs nsw nuw with
          | .val v => some (.val v)
          | .poison => none)).getD ⊤) := by
  apply foldBinary?_γRuntime_sound
  intro v hv
  cases hadd : Data.LLVM.Int.add lv rv nsw nuw with
  | poison => rw [hadd] at hv; simp at hv
  | val w => rw [hadd] at hv; simp only [Option.some.injEq] at hv; exact hv.symm

/-- `arith.muli` soundness (same template as `addi`, with `LLVM.Int.mul`). -/
theorem muli_γRuntime_sound (bw : Nat) (lv rv : Data.LLVM.Int bw) (nsw nuw : Bool) :
    (.int bw (Data.LLVM.Int.mul lv rv nsw nuw) : RuntimeValue) ∈
      γRuntime ((SparseConstantPropagation.foldBinary?
        #[.constant ⟨bw, lv⟩, .constant ⟨bw, rv⟩]
        (fun lhs rhs => match Data.LLVM.Int.mul lhs rhs nsw nuw with
          | .val v => some (.val v)
          | .poison => none)).getD ⊤) := by
  apply foldBinary?_γRuntime_sound
  intro v hv
  cases hmul : Data.LLVM.Int.mul lv rv nsw nuw with
  | poison => rw [hmul] at hv; simp at hv
  | val w => rw [hmul] at hv; simp only [Option.some.injEq] at hv; exact hv.symm

/-- `arith.subi` soundness (same template as `addi`, with `LLVM.Int.sub`). -/
theorem subi_γRuntime_sound (bw : Nat) (lv rv : Data.LLVM.Int bw) (nsw nuw : Bool) :
    (.int bw (Data.LLVM.Int.sub lv rv nsw nuw) : RuntimeValue) ∈
      γRuntime ((SparseConstantPropagation.foldBinary?
        #[.constant ⟨bw, lv⟩, .constant ⟨bw, rv⟩]
        (fun lhs rhs => match Data.LLVM.Int.sub lhs rhs nsw nuw with
          | .val v => some (.val v)
          | .poison => none)).getD ⊤) := by
  apply foldBinary?_γRuntime_sound
  intro v hv
  cases hsub : Data.LLVM.Int.sub lv rv nsw nuw with
  | poison => rw [hsub] at hv; simp at hv
  | val w => rw [hsub] at hv; simp only [Option.some.injEq] at hv; exact hv.symm

/-- `arith.andi` soundness: the interpreter's `LLVM.Int.and` propagates poison and
ANDs the bits, exactly mirroring the transfer's `andi` fold. -/
theorem andi_γRuntime_sound (bw : Nat) (lv rv : Data.LLVM.Int bw) :
    (.int bw (Data.LLVM.Int.and lv rv) : RuntimeValue) ∈
      γRuntime ((SparseConstantPropagation.foldBinary?
        #[.constant ⟨bw, lv⟩, .constant ⟨bw, rv⟩]
        (fun lhs rhs => match lhs, rhs with
          | .val lhs', .val rhs' => some (.val (BitVec.and lhs' rhs'))
          | _, _ => none)).getD ⊤) := by
  apply foldBinary?_γRuntime_sound
  intro v hv
  cases lv <;> cases rv <;> simp_all [Data.LLVM.Int.and, Id.run]

end AbstractConstant

/-!
# End-to-end soundness: instantiating `solve_sound` for constant propagation

Each value in the analysis is governed by an *equation*: an abstract transfer, a
concrete transfer over interpreter `RuntimeValue`s, and a proof the former soundly
over-approximates the latter (`Eqn.sound`). `solve_sound` then yields that the
worklist fixpoint over the whole equation system over-approximates the concrete
collecting semantics — assembling the abstract engine, the `RuntimeValue`
concretization, and the per-op soundness facts into one theorem. `constEqn`
witnesses that an `arith.constant` is a sound equation (via `γRuntime_constant`);
binary ops are analogous via `addi_γRuntime_sound` & co.
-/

namespace ConstantPropagation

open MonotoneFramework AbstractConstant

variable {K : Type} [DecidableEq K]

/-- One value's equation: abstract transfer, concrete transfer over runtime values,
and a soundness proof relating them through `γRuntime`. -/
structure Eqn (K : Type) where
  abs : (K → AbstractConstant) → AbstractConstant
  con : (K → Set RuntimeValue) → Set RuntimeValue
  sound : ∀ (σ : K → AbstractConstant) (C : K → Set RuntimeValue),
    (∀ j, C j ⊆ γRuntime (σ j)) → con C ⊆ γRuntime (abs σ)

/--
**The constant-propagation worklist solver is sound.** Its fixpoint
over-approximates the concrete collecting semantics of the equation system. This is
`MonotoneFramework.solve_sound` instantiated with each equation's transfers;
`hfsound` is discharged by the equations' own `sound` fields.
-/
theorem solve_sound (keys : List K) (hkeys : ∀ k, k ∈ keys) (eqns : K → Eqn K)
    (enqueue : K → List K)
    (hdep : ∀ (s s' : K → AbstractConstant) (a b : K),
      (∀ j, j ≠ a → s j = s' j) → (eqns b).abs s ≠ (eqns b).abs s' → b ∈ enqueue a)
    (store : K → AbstractConstant) (work : List K)
    (hinv : ∀ k', store k' ⊔ (eqns k').abs store ≠ store k' → k' ∈ work) :
    ∀ k, concreteLfp (fun C k => (eqns k).con C) k ⊆
      γRuntime (solve keys hkeys (fun k σ => (eqns k).abs σ) enqueue store work k) :=
  MonotoneFramework.solve_sound keys hkeys (fun k σ => (eqns k).abs σ) enqueue hdep store work hinv
    (fun C k => (eqns k).con C)
    (fun k => (eqns k).sound _ _ (fun _ a ha => ha))

/-- An `arith.constant` value is a sound equation: it always denotes the single
constant the interpreter produces. -/
def constEqn (bw : Nat) (v : _root_.Int) : Eqn K where
  abs _ := .constant ⟨bw, Data.LLVM.Int.constant bw v⟩
  con _ := fun rv => rv = .int bw (.val (BitVec.ofInt bw v))
  sound _ _ _ := by
    intro rv hrv
    rw [show rv = _ from hrv]
    exact γRuntime_constant bw v

/-- An `arith.addi` value is a sound equation: its concrete results are the
interpreter additions of the operands' concrete values, captured by the transfer's
`addi` fold. Operands that are `⊤` (or whose other operand is `⊤`) make the fold
yield `⊤`, which captures everything; matching constants use `addi_γRuntime_sound`.
The same shape gives `muliEqn`/`subiEqn`/`andiEqn`. -/
def addiEqn (a b : K) (bw : Nat) (nsw nuw : Bool) : Eqn K where
  abs σ := (SparseConstantPropagation.foldBinary? #[σ a, σ b]
    (fun lhs rhs => match Data.LLVM.Int.add lhs rhs nsw nuw with
      | .val v => some (.val v)
      | .poison => none)).getD ⊤
  con C := fun rv => ∃ (lv rvv : Data.LLVM.Int bw),
    (.int bw lv : RuntimeValue) ∈ C a ∧ (.int bw rvv : RuntimeValue) ∈ C b ∧
    rv = .int bw (Data.LLVM.Int.add lv rvv nsw nuw)
  sound σ C hC := by
    rintro rv ⟨lv, rvv, hCa, hCb, rfl⟩
    rcases γRuntime_int_mem (hC a hCa) with ha | ha
    · rw [ha]
      simp only [SparseConstantPropagation.foldBinary?, γRuntime]
      trivial
    · rcases γRuntime_int_mem (hC b hCb) with hb | hb
      · rw [ha, hb]
        simp only [SparseConstantPropagation.foldBinary?, γRuntime]
        trivial
      · rw [ha, hb]; exact addi_γRuntime_sound bw lv rvv nsw nuw

end ConstantPropagation

end Veir
