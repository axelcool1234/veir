module

public import Init.Data.Vector.Lemmas
public import Init.Data.Vector.OfFn
public import Init.Data.Fin.Lemmas
public import Init.Data.Order.Lemmas
public import Veir.Analysis.DataFlow.Domains.AbstractDomain

public section

namespace Veir

/-!
# Dominance domain

The Cooper-Harvey-Kennedy solver stores one dense reverse-postorder index for
each reachable block. An initialized index is an upper bound on the block's
eventual immediate-dominator index. The solver refines these bounds downward
until they stabilize.
-/

/--
Abstract dominance information for a region with `blockCount` reachable blocks.

`state` contains one immediate-dominator upper bound per block. The value
`blockCount` is the unknown bound, so it is also the scalar top value. `bottom`
represents inconsistent information and is not produced by the CHK solver.
-/
inductive DominanceValue (blockCount : Nat) where
  | bottom
  | state (immediateDominators : Vector (Fin (blockCount + 1)) blockCount)
deriving DecidableEq

namespace DominanceValue

/-- Pointwise ordering of immediate-dominator upper bounds. -/
def le : DominanceValue blockCount → DominanceValue blockCount → Prop
  | .bottom, _ => True
  | .state _, .bottom => False
  | .state lhs, .state rhs =>
      ∀ (index : Nat) (h : index < blockCount), lhs[index] ≤ rhs[index]

instance : LE (DominanceValue blockCount) where
  le := le

theorem le_def (lhs rhs : DominanceValue blockCount) :
    (lhs ≤ rhs) ↔ le lhs rhs := Iff.rfl

/-- The unknown immediate-dominator bound. -/
@[expose] def top : DominanceValue blockCount :=
  .state (Vector.replicate blockCount ⟨blockCount, by omega⟩)

instance : BoundedOrder (DominanceValue blockCount) where
  top := top
  bot := .bottom
  le_top := by
    intro value
    cases value with
    | bottom => trivial
    | state bounds =>
        intro index h
        rw [Vector.getElem_replicate]
        exact Fin.le_last bounds[index]
  bot_le := by
    intro value
    trivial

/-- Pointwise intersection of immediate-dominator index bounds. -/
def meet : DominanceValue blockCount → DominanceValue blockCount →
    DominanceValue blockCount
  | .bottom, _ => .bottom
  | _, .bottom => .bottom
  | .state lhs, .state rhs =>
      .state (Vector.ofFn fun index => min (lhs.get index) (rhs.get index))

instance : Meet (DominanceValue blockCount) where
  meet := meet

@[simp, grind .]
theorem le_refl (value : DominanceValue blockCount) : value ≤ value := by
  cases value with
  | bottom => trivial
  | state bounds =>
      intro index h
      exact Nat.le_refl bounds[index].val

@[grind →]
theorem le_trans (a b c : DominanceValue blockCount) : a ≤ b → b ≤ c → a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all [le, le_def]
  intro hab hbc index hindex
  exact Nat.le_trans (hab index hindex) (hbc index hindex)

@[grind →]
theorem le_antisymm (a b : DominanceValue blockCount) : a ≤ b → b ≤ a → a = b := by
  cases a with
  | bottom =>
      cases b <;> simp_all [le, le_def]
  | state lhs =>
      cases b with
      | bottom => simp [le, le_def]
      | state rhs =>
          intro hlr hrl
          congr 1
          apply Vector.ext
          intro index hindex
          apply Fin.eq_of_val_eq
          exact Nat.le_antisymm
            (hlr index hindex)
            (hrl index hindex)

@[simp, grind .]
theorem meet_le_left (lhs rhs : DominanceValue blockCount) : lhs ⊓ rhs ≤ lhs := by
  cases lhs with
  | bottom => trivial
  | state lhs =>
      cases rhs with
      | bottom => trivial
      | state rhs =>
          intro index hindex
          rw [Vector.getElem_ofFn]
          exact Std.min_le_left

@[simp, grind .]
theorem meet_le_right (lhs rhs : DominanceValue blockCount) : lhs ⊓ rhs ≤ rhs := by
  cases lhs with
  | bottom => trivial
  | state lhs =>
      cases rhs with
      | bottom => trivial
      | state rhs =>
          intro index hindex
          rw [Vector.getElem_ofFn]
          exact Std.min_le_right

theorem le_meet (a b c : DominanceValue blockCount) :
    c ≤ a → c ≤ b → c ≤ a ⊓ b := by
  intro hca hcb
  cases c with
  | bottom => trivial
  | state c =>
      cases a with
      | bottom => contradiction
      | state a =>
          cases b with
          | bottom => contradiction
          | state b =>
              intro index hindex
              rw [Vector.getElem_ofFn]
              exact Std.le_min_iff.mpr ⟨hca index hindex, hcb index hindex⟩

instance : MeetSemilattice (DominanceValue blockCount) where
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  meet := meet
  meet_le_left := meet_le_left
  meet_le_right := meet_le_right
  le_meet := le_meet

/--
Candidate immediate-dominator pairs represented by an abstract value. The
first component is a block and the second is one of its possible immediate
dominator indices.
-/
@[expose] def γ : DominanceValue blockCount → Set (Fin blockCount × Fin blockCount)
  | .bottom => ⊥
  | .state bounds => fun (block, dominator) => dominator.val ≤ bounds[block.val].val

theorem γ_monotone (a b : DominanceValue blockCount) : a ≤ b → γ a ⊆ γ b := by
  cases a with
  | bottom =>
      intro _ pair hpair
      exact False.elim hpair
  | state lhs =>
      cases b with
      | bottom => simp [le, le_def]
      | state rhs =>
          intro hab pair hpair
          exact Nat.le_trans hpair (hab pair.1.val pair.1.isLt)

theorem gamma_top : γ (⊤ : DominanceValue blockCount) = ⊤ := by
  funext pair
  apply propext
  change γ (top (blockCount := blockCount)) pair ↔ True
  unfold top
  simp only [γ]
  rw [Vector.getElem_replicate]
  change pair.2.val ≤ blockCount ↔ True
  simp only [iff_true]
  exact Nat.le_of_lt pair.2.isLt

theorem gamma_bot : γ (⊥ : DominanceValue blockCount) = ⊥ := rfl

instance : AbstractDomain
    (DominanceValue blockCount) (Fin blockCount × Fin blockCount) where
  γ := γ
  γ_top := gamma_top
  γ_bot := gamma_bot
  γ_monotone := γ_monotone

/-- Read the encoded immediate-dominator index, including the unknown sentinel. -/
@[inline, expose] def get! [NeZero (blockCount + 1)]
    (value : DominanceValue blockCount) (blockIndex : Nat) : Nat :=
  match value with
  | .bottom => blockCount
  | .state immediateDominators => immediateDominators[blockIndex]!.val

/-- Read an initialized immediate-dominator index. -/
@[inline, expose] def get? (value : DominanceValue blockCount) (blockIndex : Nat) : Option Nat := do
  let .state immediateDominators := value | none
  let immediateDominator ← immediateDominators[blockIndex]?
  if immediateDominator.val = blockCount then none else some immediateDominator.val

@[simp]
theorem get?_state (immediateDominators : Vector (Fin (blockCount + 1)) blockCount)
    (blockIndex : Fin blockCount) :
    (DominanceValue.state immediateDominators).get? blockIndex.val =
      if immediateDominators[blockIndex.val].val = blockCount then none
      else some immediateDominators[blockIndex.val].val := by
  simp only [get?]
  rw [getElem?_pos immediateDominators blockIndex.val blockIndex.isLt]
  rfl

theorem get!_eq_of_get?_eq_some (value : DominanceValue blockCount)
    (blockIndex immediateDominator : Fin blockCount)
    (hget : value.get? blockIndex.val = some immediateDominator.val) :
    value.get! blockIndex.val = immediateDominator.val := by
  cases value with
  | bottom => simp [get?] at hget
  | state immediateDominators =>
      simp only [get?, getElem?_pos immediateDominators blockIndex.val blockIndex.isLt] at hget
      change (if immediateDominators[blockIndex.val].val = blockCount then none else
        some immediateDominators[blockIndex.val].val) = some immediateDominator.val at hget
      split at hget
      · contradiction
      · simp only [Option.some.injEq] at hget
        simp only [get!, getElem!_pos immediateDominators blockIndex.val blockIndex.isLt]
        exact hget

/-- An in-bounds encoded parent below the unknown sentinel is initialized. -/
theorem get?_eq_some_get! (value : DominanceValue blockCount)
    (hvalue : value ≠ ⊥) (blockIndex : Fin blockCount)
    (hinitialized : value.get! blockIndex.val < blockCount) :
    value.get? blockIndex.val = some (value.get! blockIndex.val) := by
  cases value with
  | bottom => contradiction
  | state immediateDominators =>
      rw [get?_state]
      simp only [get!] at hinitialized ⊢
      rw [getElem!_pos immediateDominators blockIndex.val blockIndex.isLt] at hinitialized ⊢
      split
      · omega
      · rfl

/-- Every encoded parent is at most the unknown sentinel. -/
theorem get!_le_blockCount (value : DominanceValue blockCount)
    (blockIndex : Fin blockCount) :
    value.get! blockIndex.val ≤ blockCount := by
  cases value with
  | bottom => exact Nat.le_refl _
  | state immediateDominators =>
      simp only [get!, getElem!_pos immediateDominators blockIndex.val blockIndex.isLt]
      exact Fin.le_last immediateDominators[blockIndex.val]

/-- Two consistent values with the same encoded parent agree on the optional lookup. -/
theorem get?_eq_of_get!_eq (value1 value2 : DominanceValue blockCount)
    (hvalue1 : value1 ≠ ⊥) (hvalue2 : value2 ≠ ⊥)
    (blockIndex : Fin blockCount)
    (hagrees : value1.get! blockIndex.val = value2.get! blockIndex.val) :
    value1.get? blockIndex.val = value2.get? blockIndex.val := by
  cases value1 with
  | bottom => contradiction
  | state parents1 =>
    cases value2 with
    | bottom => contradiction
    | state parents2 =>
      rw [get?_state, get?_state]
      simp only [get!, getElem!_pos parents1 blockIndex.val blockIndex.isLt,
        getElem!_pos parents2 blockIndex.val blockIndex.isLt] at hagrees
      rw [hagrees]

private def intersectGo (value : DominanceValue blockCount) : Nat → Nat → Nat → Nat
  | 0, finger1, _ => finger1
  | fuel + 1, finger1, finger2 =>
      if finger1 = finger2 then
        finger1
      else if finger1 > finger2 then
        intersectGo value fuel (value.get! finger1) finger2
      else
        intersectGo value fuel finger1 (value.get! finger2)

/--
Find the nearest common ancestor of two initialized indices in the working
immediate-dominator forest.

Each step moves the larger RPO index to its working immediate dominator. The
solver invariant makes each movement strictly decrease. Consequently,
`index1 + index2 + 1` steps are enough for valid solver states. Fuel exhaustion
only provides total behavior for malformed values.
-/
def intersect (value : DominanceValue blockCount) (index1 index2 : Nat) : Nat :=
  intersectGo value (index1 + index2 + 1) index1 index2

private theorem intersectGo_eq_of_agree_below
    (value1 value2 : DominanceValue blockCount)
    (bound : Nat)
    (agrees : ∀ index, index < bound → value1.get! index = value2.get! index)
    (parentDecreases : ∀ index, 0 < index → index < bound → value1.get! index < index) :
    ∀ fuel index1 index2,
      index1 < bound → index2 < bound →
      intersectGo value1 fuel index1 index2 = intersectGo value2 fuel index1 index2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro _ _ _ _
      rfl
  | succ fuel ih =>
      intro index1 index2 index1Before index2Before
      simp only [intersectGo]
      by_cases same : index1 = index2
      · simp only [same, ↓reduceIte]
      · simp only [same, ↓reduceIte]
        by_cases greater : index1 > index2
        · simp only [greater, ↓reduceIte]
          have parentBefore : value1.get! index1 < bound :=
            Nat.lt_trans (parentDecreases index1 (by omega) index1Before) index1Before
          rw [← agrees index1 index1Before]
          exact ih _ _ parentBefore index2Before
        · simp only [greater, ↓reduceIte]
          have parentBefore : value1.get! index2 < bound :=
            Nat.lt_trans (parentDecreases index2 (by omega) index2Before) index2Before
          rw [← agrees index2 index2Before]
          exact ih _ _ index1Before parentBefore

/--
`intersect` only observes working-parent entries below its input bound. Later
RPO refinements therefore cannot change an earlier intersection.
-/
theorem intersect_eq_of_agree_below
    (value1 value2 : DominanceValue blockCount)
    (bound index1 index2 : Nat)
    (agrees : ∀ index, index < bound → value1.get! index = value2.get! index)
    (parentDecreases : ∀ index, 0 < index → index < bound → value1.get! index < index)
    (index1Before : index1 < bound)
    (index2Before : index2 < bound) :
    value1.intersect index1 index2 = value2.intersect index1 index2 := by
  exact intersectGo_eq_of_agree_below value1 value2 bound agrees parentDecreases _ _ _
    index1Before index2Before

/-- Reflexive transitive ancestry in the currently stored working-parent forest. -/
inductive WorkingAncestor (value : DominanceValue blockCount) : Nat → Nat → Prop where
  | refl (index : Nat) : WorkingAncestor value index index
  | parent {ancestor child : Nat} :
      WorkingAncestor value ancestor (value.get! child) →
      WorkingAncestor value ancestor child

/-- Working ancestry is transitive. -/
theorem WorkingAncestor.trans {value : DominanceValue blockCount}
    {ancestor middle descendant : Nat}
    (first : WorkingAncestor value ancestor middle)
    (second : WorkingAncestor value middle descendant) :
    WorkingAncestor value ancestor descendant := by
  induction second with
  | refl => exact first
  | parent tail ih => exact .parent ih

/-- A working ancestor is either the block itself or an ancestor of its stored parent. -/
theorem WorkingAncestor.eq_or_parent {value : DominanceValue blockCount}
    {ancestor descendant : Nat}
    (ancestry : WorkingAncestor value ancestor descendant) :
    ancestor = descendant ∨ WorkingAncestor value ancestor (value.get! descendant) := by
  cases ancestry with
  | refl => exact Or.inl rfl
  | parent tail => exact Or.inr tail

private theorem intersectGo_ancestor_inputs (value : DominanceValue blockCount)
    (valid : Nat → Prop)
    (parentValid : ∀ index, valid index → valid (value.get! index))
    (parentDecreases : ∀ index, valid index → 0 < index → value.get! index < index) :
    ∀ fuel index1 index2,
      valid index1 → valid index2 → index1 + index2 < fuel →
      WorkingAncestor value (intersectGo value fuel index1 index2) index1 ∧
        WorkingAncestor value (intersectGo value fuel index1 index2) index2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro index1 index2 _ _ hfuel
      omega
  | succ fuel ih =>
      intro index1 index2 hvalid1 hvalid2 hfuel
      simp only [intersectGo]
      split
      · rename_i heq
        subst index2
        exact ⟨WorkingAncestor.refl index1, WorkingAncestor.refl index1⟩
      · split
        · rename_i hgreater
          have hpositive : 0 < index1 := Nat.zero_lt_of_lt hgreater
          have hdecreases := parentDecreases index1 hvalid1 hpositive
          have hnextFuel : value.get! index1 + index2 < fuel := by omega
          have result := ih _ _ (parentValid index1 hvalid1) hvalid2 hnextFuel
          exact ⟨WorkingAncestor.parent result.1, result.2⟩
        · rename_i hnotGreater
          have hless : index1 < index2 := by omega
          have hpositive : 0 < index2 := Nat.zero_lt_of_lt hless
          have hdecreases := parentDecreases index2 hvalid2 hpositive
          have hnextFuel : index1 + value.get! index2 < fuel := by omega
          have result := ih _ _ hvalid1 (parentValid index2 hvalid2) hnextFuel
          exact ⟨result.1, WorkingAncestor.parent result.2⟩

/-- `intersect` returns a working ancestor of each initialized input. -/
theorem intersect_ancestor_inputs (value : DominanceValue blockCount)
    (valid : Nat → Prop)
    (parentValid : ∀ index, valid index → valid (value.get! index))
    (parentDecreases : ∀ index, valid index → 0 < index → value.get! index < index)
    (hindex1 : valid index1) (hindex2 : valid index2) :
    WorkingAncestor value (value.intersect index1 index2) index1 ∧
      WorkingAncestor value (value.intersect index1 index2) index2 := by
  exact intersectGo_ancestor_inputs value valid parentValid parentDecreases _ index1 index2
    hindex1 hindex2 (Nat.lt_succ_self _)

private theorem intersectGo_preserves (value : DominanceValue blockCount)
    (property : Nat → Prop)
    (step : ∀ index, property index → property (value.get! index)) :
    ∀ fuel index1 index2,
      property index1 → property index2 →
      property (intersectGo value fuel index1 index2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro index1 index2 hindex1 _
      exact hindex1
  | succ fuel ih =>
      intro index1 index2 hindex1 hindex2
      simp only [intersectGo]
      split
      · exact hindex1
      · split
        · exact ih _ _ (step index1 hindex1) hindex2
        · exact ih _ _ hindex1 (step index2 hindex2)

/-- Any property preserved by working-parent steps is preserved by `intersect`. -/
theorem intersect_preserves (value : DominanceValue blockCount)
    (property : Nat → Prop)
    (step : ∀ index, property index → property (value.get! index))
    (hindex1 : property index1) (hindex2 : property index2) :
    property (value.intersect index1 index2) := by
  exact intersectGo_preserves value property step _ index1 index2 hindex1 hindex2

private theorem intersectGo_preserves_above (value : DominanceValue blockCount)
    (root : Nat) (property : Nat → Prop)
    (lowerBound : ∀ index, property index → root ≤ index)
    (step : ∀ index, root < index → property index → property (value.get! index)) :
    ∀ fuel index1 index2,
      property index1 → property index2 →
      property (intersectGo value fuel index1 index2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro index1 index2 hindex1 _
      exact hindex1
  | succ fuel ih =>
      intro index1 index2 hindex1 hindex2
      simp only [intersectGo]
      split
      · exact hindex1
      · rename_i hne
        split
        · rename_i hgreater
          have habove : root < index1 :=
            Nat.lt_of_le_of_lt (lowerBound index2 hindex2) hgreater
          exact ih _ _ (step index1 habove hindex1) hindex2
        · rename_i hnotGreater
          have hless : index1 < index2 :=
            Nat.lt_of_le_of_ne (Nat.le_of_not_gt hnotGreater) hne
          have habove : root < index2 :=
            Nat.lt_of_le_of_lt (lowerBound index1 hindex1) hless
          exact ih _ _ hindex1 (step index2 habove hindex2)

/--
Any property whose indices lie at or above `root`, and which survives parent
steps strictly above `root`, is preserved by `intersect`.
-/
theorem intersect_preserves_above (value : DominanceValue blockCount)
    (root : Nat) (property : Nat → Prop)
    (lowerBound : ∀ index, property index → root ≤ index)
    (step : ∀ index, root < index → property index → property (value.get! index))
    (hindex1 : property index1) (hindex2 : property index2) :
    property (value.intersect index1 index2) := by
  exact intersectGo_preserves_above value root property lowerBound step _ index1 index2
    hindex1 hindex2

private theorem intersectGo_le_inputs (value : DominanceValue blockCount)
    (valid : Nat → Prop)
    (parentValid : ∀ index, valid index → valid (value.get! index))
    (parentDecreases : ∀ index, valid index → 0 < index → value.get! index < index) :
    ∀ fuel index1 index2,
      valid index1 → valid index2 → index1 + index2 < fuel →
      intersectGo value fuel index1 index2 ≤ index1 ∧
        intersectGo value fuel index1 index2 ≤ index2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro index1 index2 _ _ hfuel
      omega
  | succ fuel ih =>
      intro index1 index2 hvalid1 hvalid2 hfuel
      simp only [intersectGo]
      split
      · rename_i heq
        omega
      · split
        · rename_i hgreater
          have hpositive : 0 < index1 := Nat.zero_lt_of_lt hgreater
          have hdecreases := parentDecreases index1 hvalid1 hpositive
          have hnextFuel : value.get! index1 + index2 < fuel := by omega
          have result := ih _ _ (parentValid index1 hvalid1) hvalid2 hnextFuel
          exact ⟨Nat.le_trans result.1 (Nat.le_of_lt hdecreases), result.2⟩
        · rename_i hnotGreater
          have hless : index1 < index2 := by omega
          have hpositive : 0 < index2 := Nat.zero_lt_of_lt hless
          have hdecreases := parentDecreases index2 hvalid2 hpositive
          have hnextFuel : index1 + value.get! index2 < fuel := by omega
          have result := ih _ _ hvalid1 (parentValid index2 hvalid2) hnextFuel
          exact ⟨result.1, Nat.le_trans result.2 (Nat.le_of_lt hdecreases)⟩

/-- In a strictly descending parent forest, `intersect` is no greater than either input. -/
theorem intersect_le_inputs (value : DominanceValue blockCount)
    (valid : Nat → Prop)
    (parentValid : ∀ index, valid index → valid (value.get! index))
    (parentDecreases : ∀ index, valid index → 0 < index → value.get! index < index)
    (hindex1 : valid index1) (hindex2 : valid index2) :
    value.intersect index1 index2 ≤ index1 ∧
      value.intersect index1 index2 ≤ index2 := by
  exact intersectGo_le_inputs value valid parentValid parentDecreases _ index1 index2
    hindex1 hindex2 (Nat.lt_succ_self _)

/-- Meet one block's current bound with an initialized immediate-dominator index. -/
@[inline, expose] def refine!
    (value : DominanceValue blockCount) (blockIndex immediateDominator : Nat) :
    DominanceValue blockCount :=
  match value with
  | .bottom => .bottom
  | .state immediateDominators =>
      if h : immediateDominator < blockCount then
        let oldImmediateDominator := immediateDominators[blockIndex]!.val
        let refinedImmediateDominator := min oldImmediateDominator immediateDominator
        .state (immediateDominators.set! blockIndex ⟨refinedImmediateDominator, by omega⟩)
      else
        value

/-- Refining one in-bounds block moves the region state downward. -/
theorem refine_le (value : DominanceValue blockCount)
    (hblock : blockIndex < blockCount) (immediateDominator : Nat) :
    value.refine! blockIndex immediateDominator ≤ value := by
  cases value with
  | bottom => trivial
  | state immediateDominators =>
      by_cases hdominator : immediateDominator < blockCount
      · simp only [refine!, hdominator, dite_eq_left]
        intro index hindex
        rw [Vector.getElem_set! hindex]
        split
        · subst index
          simp only [getElem!_pos immediateDominators blockIndex hblock]
          exact Nat.min_le_left _ _
        · exact Nat.le_refl immediateDominators[index].val
      · simp only [refine!, hdominator]
        exact le_refl _

/-- Refinement preserves a consistent region state. -/
theorem refine_ne_bottom (value : DominanceValue blockCount)
    (hvalue : value ≠ ⊥) (blockIndex immediateDominator : Nat) :
    value.refine! blockIndex immediateDominator ≠ ⊥ := by
  cases value with
  | bottom => contradiction
  | state immediateDominators =>
      simp only [refine!]
      split <;> simp

/-- Refining a block can only remove represented immediate-dominator candidates. -/
theorem gamma_refine_subset (value : DominanceValue blockCount)
    (hblock : blockIndex < blockCount) (immediateDominator : Nat) :
    γ (value.refine! blockIndex immediateDominator) ⊆ γ value :=
  γ_monotone _ _ (refine_le value hblock immediateDominator)

/-- Reading a valid refinement returns the meet of the old and incoming bounds. -/
theorem get_refine_eq_min (value : DominanceValue blockCount)
    (hvalue : value ≠ ⊥) (hblock : blockIndex < blockCount)
    (hdominator : immediateDominator < blockCount) :
    (value.refine! blockIndex immediateDominator).get! blockIndex =
      min (value.get! blockIndex) immediateDominator := by
  cases value with
  | bottom => contradiction
  | state immediateDominators =>
      simp only [refine!, hdominator, dite_eq_left, get!]
      rw [getElem!_pos (immediateDominators.set! blockIndex _) blockIndex hblock]
      rw [Vector.getElem_set!_self]

/-- A refinement is a no-op when the current bound already equals the meet. -/
theorem refine_eq_self_of_get_eq_min (value : DominanceValue blockCount)
    (hvalue : value ≠ ⊥)
    (hblock : blockIndex < blockCount)
    (hdominator : immediateDominator < blockCount)
    (unchanged : value.get! blockIndex =
      min (value.get! blockIndex) immediateDominator) :
    value.refine! blockIndex immediateDominator = value := by
  cases value with
  | bottom => contradiction
  | state immediateDominators =>
    simp only [refine!, hdominator, dite_eq_left, get!] at unchanged ⊢
    rw [getElem!_pos immediateDominators blockIndex hblock] at unchanged
    congr 1
    apply Vector.ext
    intro index indexInBounds
    rw [Vector.getElem_set! indexInBounds]
    split
    · rename_i sameIndex
      subst index
      apply Fin.eq_of_val_eq
      change min immediateDominators[blockIndex]!.val immediateDominator =
        immediateDominators[blockIndex].val
      rw [getElem!_pos immediateDominators blockIndex hblock]
      exact unchanged.symm
    · rfl

/-- Refining one block leaves every other initialized-parent lookup unchanged. -/
theorem get?_refine_of_ne (value : DominanceValue blockCount)
    (hvalue : value ≠ ⊥) (blockIndex queriedIndex immediateDominator : Fin blockCount)
    (hne : queriedIndex ≠ blockIndex) :
    (value.refine! blockIndex.val immediateDominator.val).get? queriedIndex.val =
      value.get? queriedIndex.val := by
  cases value with
  | bottom => contradiction
  | state immediateDominators =>
      simp only [refine!, immediateDominator.isLt, dite_eq_left, get?_state]
      rw [Vector.getElem_set!]
      split
      · rename_i heq
        exact False.elim (hne (Fin.eq_of_val_eq heq.symm))
      · rfl

/-- Refining one block leaves every other encoded-parent lookup unchanged. -/
theorem get!_refine_of_ne (value : DominanceValue blockCount)
    (hvalue : value ≠ ⊥) (blockIndex queriedIndex immediateDominator : Fin blockCount)
    (hne : queriedIndex ≠ blockIndex) :
    (value.refine! blockIndex.val immediateDominator.val).get! queriedIndex.val =
      value.get! queriedIndex.val := by
  cases value with
  | bottom => contradiction
  | state immediateDominators =>
      simp only [refine!, immediateDominator.isLt, dite_eq_left, get!,
        getElem!_pos immediateDominators queriedIndex.val queriedIndex.isLt]
      rw [getElem!_pos (immediateDominators.set! blockIndex.val _) queriedIndex.val
        queriedIndex.isLt, Vector.getElem_set!]
      split
      · rename_i heq
        exact False.elim (hne (Fin.eq_of_val_eq heq.symm))
      · rfl

/-- Refining a block initializes it to the minimum of its old and incoming bounds. -/
theorem get?_refine_eq_some_min (value : DominanceValue blockCount)
    (hvalue : value ≠ ⊥) (blockIndex immediateDominator : Fin blockCount) :
    (value.refine! blockIndex.val immediateDominator.val).get? blockIndex.val =
      some (min (value.get! blockIndex.val) immediateDominator.val) := by
  cases value with
  | bottom => contradiction
  | state immediateDominators =>
      simp only [refine!, immediateDominator.isLt, dite_eq_left, get?_state, get!]
      rw [Vector.getElem_set!_self]
      simp only [ite_eq_right_iff]
      intro heq
      have hle := Nat.min_le_right immediateDominators[blockIndex.val]!.val
        immediateDominator.val
      omega

/-- Initial CHK state: only the entry block at RPO index zero is initialized. -/
@[expose] def initial (blockCount : Nat) : DominanceValue blockCount :=
  (⊤ : DominanceValue blockCount).refine! 0 0

theorem get?_initial [NeZero blockCount] (blockIndex : Fin blockCount) :
    (initial blockCount).get? blockIndex.val =
      if blockIndex.val = 0 then some 0 else none := by
  have hpositive : 0 < blockCount := Nat.pos_of_neZero blockCount
  unfold initial
  change ((top (blockCount := blockCount)).refine! 0 0).get? blockIndex.val = _
  unfold top
  simp only [refine!, hpositive, dite_eq_left, get?_state]
  rw [Vector.getElem_set!]
  split
  · rename_i hzero
    have hbzero : blockIndex.val = 0 := hzero.symm
    simp [hbzero, hpositive]
    exact Nat.ne_of_lt hpositive
  · rw [Vector.getElem_replicate]
    rename_i hne
    have hbne : blockIndex.val ≠ 0 := by
      intro hzero
      exact hne hzero.symm
    simp [hbne]

end DominanceValue

end Veir
