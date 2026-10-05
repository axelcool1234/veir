module

public import Veir.Analysis.DataFlow.Domains.AbstractDomain

public section

namespace Veir

/-!
# Dominance domain

A descending abstract domain of candidate dominators. An abstract value maps
each block to the set of blocks that may still dominate it. The order is
pointwise set inclusion, top contains every candidate, and meet intersects
candidate sets.
-/

/-- Candidate dominators for every block in a control flow graph. -/
structure DominanceDomain (Block : Type) where
  dominators : Block → Set Block

namespace DominanceDomain

/-- Pointwise inclusion of candidate dominator sets. -/
def le (lhs rhs : DominanceDomain Block) : Prop :=
  ∀ block, lhs.dominators block ⊆ rhs.dominators block

instance : LE (DominanceDomain Block) where
  le := le

theorem le_def (lhs rhs : DominanceDomain Block) : (lhs ≤ rhs) ↔ le lhs rhs := Iff.rfl

@[ext]
theorem ext (lhs rhs : DominanceDomain Block)
    (h : ∀ block dominator,
      dominator ∈ lhs.dominators block ↔ dominator ∈ rhs.dominators block) :
    lhs = rhs := by
  cases lhs with
  | mk lhs =>
    cases rhs with
    | mk rhs =>
      congr
      funext block dominator
      apply propext
      exact h block dominator

@[simp, grind .]
theorem le_refl (value : DominanceDomain Block) : value ≤ value := by
  intro _ _ h
  exact h

@[grind →]
theorem le_trans (a b c : DominanceDomain Block) : a ≤ b → b ≤ c → a ≤ c := by
  intro hab hbc block _ h
  exact hbc block (hab block h)

@[grind →]
theorem le_antisymm (a b : DominanceDomain Block) : a ≤ b → b ≤ a → a = b := by
  intro hab hba
  apply ext
  intro block dominator
  constructor
  · intro h
    exact hab block h
  · intro h
    exact hba block h

instance : BoundedOrder (DominanceDomain Block) where
  top := { dominators := fun _ => ⊤ }
  bot := { dominators := fun _ => ⊥ }
  le_top := by
    intro _ _ _ _
    trivial
  bot_le := by
    intro _ _ _ h
    exact False.elim h

/-- Intersect the candidate dominators of each block. -/
def meet (lhs rhs : DominanceDomain Block) : DominanceDomain Block :=
  { dominators := fun block dominator =>
      dominator ∈ lhs.dominators block ∧ dominator ∈ rhs.dominators block }

instance : Meet (DominanceDomain Block) where
  meet := meet

@[simp, grind .]
theorem meet_le_left (lhs rhs : DominanceDomain Block) : lhs ⊓ rhs ≤ lhs := by
  intro _ _ h
  exact h.1

@[simp, grind .]
theorem meet_le_right (lhs rhs : DominanceDomain Block) : lhs ⊓ rhs ≤ rhs := by
  intro _ _ h
  exact h.2

theorem le_meet (a b c : DominanceDomain Block) : c ≤ a → c ≤ b → c ≤ a ⊓ b := by
  intro hca hcb block _ h
  exact ⟨hca block h, hcb block h⟩

instance : MeetSemilattice (DominanceDomain Block) where
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  meet := meet
  meet_le_left := meet_le_left
  meet_le_right := meet_le_right
  le_meet := le_meet

/--
The concrete dominance pairs represented by an abstract value. A pair consists
of a candidate dominator followed by the block it may dominate.
-/
@[expose] def γ (value : DominanceDomain Block) : Set (Block × Block) :=
  fun (dominator, block) => dominator ∈ value.dominators block

theorem γ_monotone (a b : DominanceDomain Block) : a ≤ b → γ a ⊆ γ b := by
  intro hab pair h
  exact hab pair.2 h

instance : AbstractDomain (DominanceDomain Block) (Block × Block) where
  γ := γ
  γ_top := rfl
  γ_bot := rfl
  γ_monotone := γ_monotone

end DominanceDomain

end Veir
