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
def top : DominanceValue blockCount :=
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
@[inline] def get! [NeZero (blockCount + 1)]
    (value : DominanceValue blockCount) (blockIndex : Nat) : Nat :=
  match value with
  | .bottom => blockCount
  | .state immediateDominators => immediateDominators[blockIndex]!.val

/-- Read an initialized immediate-dominator index. -/
@[inline] def get? (value : DominanceValue blockCount) (blockIndex : Nat) : Option Nat := do
  let .state immediateDominators := value | none
  let immediateDominator ← immediateDominators[blockIndex]?
  if immediateDominator.val = blockCount then none else some immediateDominator.val

/-- Meet one block's current bound with an initialized immediate-dominator index. -/
@[inline] def refine! (value : DominanceValue blockCount) (blockIndex immediateDominator : Nat) :
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

end DominanceValue

end Veir
