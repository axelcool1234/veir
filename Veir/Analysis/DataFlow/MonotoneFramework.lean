module

public import Veir.Analysis.DataFlow.Domains.AbstractDomain

public section

namespace Veir

namespace MonotoneFramework

/-!
# The monotone framework: terminating fixpoint iteration

This is the abstract engine behind every monotone dataflow analysis. Given a
*monotone* endofunction `f` on a lattice of *finite height*, Kleene iteration
`⊥, f ⊥, f² ⊥, …` reaches a fixpoint after finitely many steps.

`iterateFrom` performs that iteration. It is an ordinary (non-`partial`)
definition: Lean accepts it only because the recursion is well-founded, so the
fact that it elaborates *is* the termination proof — the finite-height `rank` is
the strictly increasing quantity and `maxRank` bounds it, so `maxRank - rank` is
the strictly decreasing measure. `iterateFrom_isFixpoint` and
`iterateFrom_le_of_fixpoint` then show the result is the least fixpoint above the
starting point, and `iterateFrom_preserves` lifts any `f`-closed predicate (e.g.
γ-soundness) to the computed fixpoint.

Connecting this engine to the concrete worklist solver (`run`) is a separate,
larger step: `run` would need to be re-expressed as well-founded recursion over a
potential function on the whole `DataFlowContext`, with each analysis carrying a
monotonicity contract. The theorems here are the reusable core that step targets.
-/

variable {α : Type}

/-- An endofunction is monotone when it preserves the lattice order. -/
def Monotone [LE α] (f : α → α) : Prop := ∀ ⦃a b : α⦄, a ≤ b → f a ≤ f b

-- `h` in the body below is used by `decreasing_by`, which the linter misses.
set_option linter.unusedVariables false in
/--
Iterate `f` upward starting from `x`, assuming `x ≤ f x`, until a fixpoint is
reached.

Terminates because each non-trivial step strictly increases `FiniteHeight.rank`
(`x < f x`), and `rank` is bounded above by `FiniteHeight.maxRank`.
-/
def iterateFrom [LE α] [DecidableEq α] [FiniteHeight α]
    (f : α → α) (hf : Monotone f) : (x : α) → x ≤ f x → α
  | x, hx =>
    if h : f x = x then
      x
    else
      iterateFrom f hf (f x) (hf hx)
termination_by x => FiniteHeight.maxRank (α := α) - FiniteHeight.rank x
decreasing_by
  have hne : x ≠ f x := fun he => h he.symm
  have hlt : FiniteHeight.rank x < FiniteHeight.rank (f x) :=
    FiniteHeight.rank_lt_of_lt hx hne
  have hle : FiniteHeight.rank (f x) ≤ FiniteHeight.maxRank (α := α) :=
    FiniteHeight.rank_le_maxRank (f x)
  omega

/-- `iterateFrom` returns a fixpoint of `f`. -/
theorem iterateFrom_isFixpoint [LE α] [DecidableEq α] [FiniteHeight α]
    (f : α → α) (hf : Monotone f) :
    ∀ (x : α) (hx : x ≤ f x), f (iterateFrom f hf x hx) = iterateFrom f hf x hx
  | x, hx => by
    rw [iterateFrom]
    by_cases h : f x = x
    · rw [dif_pos h]; exact h
    · rw [dif_neg h]; exact iterateFrom_isFixpoint f hf (f x) (hf hx)
termination_by x _ => FiniteHeight.maxRank (α := α) - FiniteHeight.rank x
decreasing_by
  have hne : x ≠ f x := fun he => h he.symm
  have hlt := FiniteHeight.rank_lt_of_lt hx hne
  have hle := FiniteHeight.rank_le_maxRank (f x)
  omega

/-- The result of `iterateFrom` is below every fixpoint `p` above the start. -/
theorem iterateFrom_le_of_fixpoint [LE α] [DecidableEq α] [FiniteHeight α]
    (f : α → α) (hf : Monotone f) (p : α) (hp : f p = p) :
    ∀ (x : α) (hx : x ≤ f x), x ≤ p → iterateFrom f hf x hx ≤ p
  | x, hx => by
    intro hxp
    rw [iterateFrom]
    by_cases h : f x = x
    · rw [dif_pos h]; exact hxp
    · rw [dif_neg h]
      exact iterateFrom_le_of_fixpoint f hf p hp (f x) (hf hx) (hp ▸ hf hxp)
termination_by x _ => FiniteHeight.maxRank (α := α) - FiniteHeight.rank x
decreasing_by
  have hne : x ≠ f x := fun he => h he.symm
  have hlt := FiniteHeight.rank_lt_of_lt hx hne
  have hle := FiniteHeight.rank_le_maxRank (f x)
  omega

/--
Any predicate closed under `f` and holding at the start also holds at the
computed fixpoint. This is the abstract soundness engine: instantiate `P` with a
γ-soundness predicate to transport soundness through the whole iteration.
-/
theorem iterateFrom_preserves [LE α] [DecidableEq α] [FiniteHeight α]
    (f : α → α) (hf : Monotone f) (P : α → Prop)
    (hstep : ∀ a, P a → P (f a)) :
    ∀ (x : α) (hx : x ≤ f x), P x → P (iterateFrom f hf x hx)
  | x, hx => by
    intro hPx
    rw [iterateFrom]
    by_cases h : f x = x
    · rw [dif_pos h]; exact hPx
    · rw [dif_neg h]
      exact iterateFrom_preserves f hf P hstep (f x) (hf hx) (hstep x hPx)
termination_by x _ => FiniteHeight.maxRank (α := α) - FiniteHeight.rank x
decreasing_by
  have hne : x ≠ f x := fun he => h he.symm
  have hlt := FiniteHeight.rank_lt_of_lt hx hne
  have hle := FiniteHeight.rank_le_maxRank (f x)
  omega

/-- The least fixpoint of a monotone `f`, computed by iterating from `⊥`. -/
def lfp [LE α] [DecidableEq α] [BoundedOrder α] [FiniteHeight α]
    (f : α → α) (hf : Monotone f) : α :=
  iterateFrom f hf ⊥ (OrderBot.bot_le (f ⊥))

/-- `lfp f` is a fixpoint of `f`. -/
theorem lfp_isFixpoint [LE α] [DecidableEq α] [BoundedOrder α] [FiniteHeight α]
    (f : α → α) (hf : Monotone f) : f (lfp f hf) = lfp f hf :=
  iterateFrom_isFixpoint f hf ⊥ (OrderBot.bot_le (f ⊥))

/-- `lfp f` is the least fixpoint: it is below every other fixpoint. -/
theorem lfp_least [LE α] [DecidableEq α] [BoundedOrder α] [FiniteHeight α]
    (f : α → α) (hf : Monotone f) (p : α) (hp : f p = p) : lfp f hf ≤ p :=
  iterateFrom_le_of_fixpoint f hf p hp ⊥ (OrderBot.bot_le (f ⊥)) (OrderBot.bot_le p)

/--
Soundness of the least fixpoint: any predicate that holds at `⊥` and is preserved
by `f` holds at `lfp f`.
-/
theorem lfp_preserves [LE α] [DecidableEq α] [BoundedOrder α] [FiniteHeight α]
    (f : α → α) (hf : Monotone f) (P : α → Prop)
    (hbot : P ⊥) (hstep : ∀ a, P a → P (f a)) : P (lfp f hf) :=
  iterateFrom_preserves f hf P hstep ⊥ (OrderBot.bot_le (f ⊥)) hbot

/-!
## A terminating worklist solver

`iterateFrom` re-applies `f` to the *whole* state each round. A real solver
(`DataFlowFramework.run`) instead keeps a *worklist* of keys to recompute and
revisits a key's dependents only when its value changes. This section proves that
the worklist discipline still terminates — without `partial`, without fuel — which
is the abstract justification for making `run` a total definition.

The termination measure is lexicographic: `(potential store, worklist length)`.
A productive step (a key's value strictly rises) strictly lowers the potential; an
unproductive step (no change) leaves the potential fixed but shortens the
worklist. Finite height bounds the potential, so neither can happen forever.
-/

/-- Helper: a pointwise-`≤` map gives a `≤` sum. -/
private theorem sumMap_le {β : Type} {g h : β → Nat} :
    ∀ {l : List β}, (∀ x ∈ l, g x ≤ h x) → (l.map g).sum ≤ (l.map h).sum
  | [], _ => Nat.le_refl 0
  | a :: t, hle => by
    simp only [List.map_cons, List.sum_cons]
    have ht := @sumMap_le β g h t (fun x hx => hle x (by simp [hx]))
    have ha := hle a (by simp)
    omega

/-- Helper: pointwise-`≤` plus one strict point gives a strict sum. -/
private theorem sumMap_lt {β : Type} {g h : β → Nat} {k : β} :
    ∀ {l : List β}, (∀ x ∈ l, g x ≤ h x) → k ∈ l → g k < h k →
      (l.map g).sum < (l.map h).sum
  | [], _, hk, _ => by simp at hk
  | a :: t, hle, hk, hklt => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hk with rfl | hkt
    · have ht := sumMap_le (g := g) (h := h) (l := t) (fun x hx => hle x (by simp [hx]))
      omega
    · have ha := hle a (by simp)
      have ht := sumMap_lt (l := t) (fun x hx => hle x (by simp [hx])) hkt hklt
      omega

section Worklist

variable {K L : Type} [DecidableEq K]

/-- The remaining "rising capacity" of the whole store: the sum, over all keys,
of how far each key's value can still climb. Strictly decreases on a productive
step. -/
def potential [LE L] [FiniteHeight L] (keys : List K) (store : K → L) : Nat :=
  (keys.map (fun k => FiniteHeight.maxRank (α := L) - FiniteHeight.rank (store k))).sum

/-- Functional update of a store at one key. -/
def update (store : K → L) (k : K) (v : L) : K → L :=
  fun k' => if k' = k then v else store k'

@[simp] theorem update_self (store : K → L) (k : K) (v : L) : update store k v k = v := by
  simp [update]

theorem update_ne (store : K → L) (k : K) (v : L) {k' : K} (h : k' ≠ k) :
    update store k v k' = store k' := by
  simp [update, h]

/-- Raising one key's value (to a strictly higher rank) strictly lowers the
potential. -/
theorem potential_update_lt [LE L] [FiniteHeight L]
    (keys : List K) (store : K → L) (k : K) (v : L)
    (hk : k ∈ keys) (hraise : FiniteHeight.rank (store k) ≤ FiniteHeight.rank v)
    (hstrict : FiniteHeight.rank (store k) < FiniteHeight.rank v) :
    potential keys (update store k v) < potential keys store := by
  apply sumMap_lt (k := k)
  · intro x _
    by_cases hxk : x = k
    · subst hxk; rw [update_self]; omega
    · rw [update_ne store k v hxk]; omega
  · exact hk
  · rw [update_self]
    have := FiniteHeight.rank_le_maxRank (α := L) v
    omega

-- `h` in the body is used by `decreasing_by`, which the linter misses.
set_option linter.unusedVariables false in
/--
A worklist fixpoint solver, as a **total** (non-`partial`) definition.

`f k store` recomputes key `k`'s candidate from the current store; the candidate
is joined into `store k`, and on a strict increase the new value is written and
`k`'s dependents (`enqueue k`) are re-added to the worklist. `hkeys` says `keys`
enumerates every key, so a productive step always lowers `potential keys`.

Termination (which is the whole point — `DataFlowFramework.run` is the same loop
written with `partial`) holds by the lexicographic measure
`(potential keys store, work.length)`: a strict increase lowers the potential; a
no-op shortens the worklist; finite height bounds the potential.
-/
def solve [LE L] [DecidableEq L] [JoinSemilattice L] [FiniteHeight L]
    (keys : List K) (hkeys : ∀ k, k ∈ keys)
    (f : K → (K → L) → L) (enqueue : K → List K) :
    (K → L) → List K → (K → L)
  | store, [] => store
  | store, k :: rest =>
    if h : store k ⊔ f k store = store k then
      solve keys hkeys f enqueue store rest
    else
      solve keys hkeys f enqueue (update store k (store k ⊔ f k store)) (rest ++ enqueue k)
termination_by store work => (potential keys store, work.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · refine Prod.Lex.left _ _ ?_
    have hstrict : FiniteHeight.rank (store k) < FiniteHeight.rank (store k ⊔ f k store) :=
      FiniteHeight.rank_lt_of_lt (JoinSemilattice.le_join_left _ _) (fun he => h he.symm)
    exact potential_update_lt keys store k _ (hkeys k) (Nat.le_of_lt hstrict) hstrict

/-- Join absorption: `(a ⊔ b) ⊔ b = a ⊔ b`. -/
theorem join_absorb [LE L] [JoinSemilattice L] (a b : L) : (a ⊔ b) ⊔ b = a ⊔ b := by
  apply Std.IsPartialOrder.le_antisymm
  · exact JoinSemilattice.join_le _ _ _ (Std.IsPreorder.le_refl _) (JoinSemilattice.le_join_right a b)
  · exact JoinSemilattice.le_join_left _ _

/--
**The worklist solver reaches a fixpoint.** When `solve` returns (worklist empty),
every key satisfies its dataflow equation: `f k result ≤ result k`. Combined with
`solve`'s termination, this is the full correctness of the worklist discipline —
the result is a post-fixpoint of the equation system.

This needs `enqueue` to be *dependency-complete* (`hdep`): if changing the store at
`a` could change `f b`, then `b ∈ enqueue a`. That is exactly the contract a real
analysis' "enqueue this fact's dependents on change" must satisfy, and it is what
lets an empty worklist certify that no key's value would still move.

The invariant carried through the recursion is "every key whose equation is
currently violated is on the worklist"; a productive update re-enqueues precisely
the dependents that `hdep` guarantees cover every newly-violated key, and join
absorption shows the updated key itself settles.
-/
theorem solve_postfixpoint [LE L] [DecidableEq L] [JoinSemilattice L] [FiniteHeight L]
    (keys : List K) (hkeys : ∀ k, k ∈ keys) (f : K → (K → L) → L) (enqueue : K → List K)
    (hdep : ∀ (s s' : K → L) (a b : K),
      (∀ j, j ≠ a → s j = s' j) → f b s ≠ f b s' → b ∈ enqueue a) :
    ∀ (store : K → L) (work : List K),
      (∀ k', store k' ⊔ f k' store ≠ store k' → k' ∈ work) →
      ∀ k, f k (solve keys hkeys f enqueue store work) ≤ (solve keys hkeys f enqueue store work) k := by
  intro store work
  induction store, work using solve.induct keys hkeys f enqueue with
  | case1 store =>
    intro hinv k
    have heq : store k ⊔ f k store = store k := by
      by_cases h : store k ⊔ f k store = store k
      · exact h
      · exact absurd (hinv k h) (by simp)
    have hle : f k store ≤ store k := heq ▸ JoinSemilattice.le_join_right (store k) (f k store)
    simp only [solve]
    exact hle
  | case2 store k rest h ih =>
    intro hinv
    rw [solve, dif_pos h]
    refine ih (fun k' hviol => ?_)
    rcases List.mem_cons.1 (hinv k' hviol) with rfl | h'
    · exact absurd h hviol
    · exact h'
  | case3 store k rest h ih =>
    intro hinv
    rw [solve, dif_neg h]
    refine ih (fun k' hviol => ?_)
    by_cases hfeq : f k' (update store k (store k ⊔ f k store)) = f k' store
    · by_cases hk'k : k' = k
      · subst hk'k
        rw [update_self, hfeq] at hviol
        exact absurd (join_absorb (store k') (f k' store)) hviol
      · rw [update_ne store k _ hk'k, hfeq] at hviol
        refine List.mem_append.mpr (Or.inl ?_)
        rcases List.mem_cons.1 (hinv k' hviol) with rfl | h'
        · exact absurd rfl hk'k
        · exact h'
    · exact List.mem_append.mpr (Or.inr (hdep store (update store k (store k ⊔ f k store)) k k'
        (fun j hj => (update_ne store k _ hj).symm) (Ne.symm hfeq)))

end Worklist

/-!
## Soundness of a post-fixpoint

The worklist computes an abstract *post-fixpoint* (`solve_postfixpoint`). The final
step of dataflow correctness is that a post-fixpoint whose transfer soundly
abstracts the concrete semantics over-approximates the *concrete collecting
semantics* — so the analysis result is sound.

We model the concrete collecting semantics as the least post-fixpoint of a concrete
transfer `Fc` over `K → Set Concrete` (`concreteLfp`, the intersection of all
`Fc`-closed concrete stores). Leastness is definitional, so no complete-lattice
fixpoint machinery is needed: soundness follows because `γ ∘ σ` is itself a concrete
post-fixpoint (using `γ_monotone` on the abstract post-fixpoint and the transfer's
soundness `hfsound`), hence above the least one.
-/

section Soundness

variable {K L Concrete : Type} [LE L] [AbstractDomain L Concrete]

/-- The concrete collecting semantics: the least post-fixpoint of the concrete
transfer `Fc`, i.e. the intersection of every concrete store closed under `Fc`. -/
def concreteLfp (Fc : (K → Set Concrete) → K → Set Concrete) : K → Set Concrete :=
  fun k cval => ∀ y : K → Set Concrete, (∀ j, Fc y j ⊆ y j) → cval ∈ y k

/--
**Soundness of an abstract post-fixpoint.** If `σ` is an abstract post-fixpoint
(`f k σ ≤ σ k`) and the abstract transfer `f` soundly abstracts the concrete
transfer `Fc` at `σ` (`hfsound`), then `σ` over-approximates the concrete collecting
semantics: every concrete value a key can take lies in that key's concretization.
-/
theorem postfixpoint_sound (f : K → (K → L) → L) (σ : K → L)
    (Fc : (K → Set Concrete) → K → Set Concrete)
    (hpost : ∀ k, f k σ ≤ σ k)
    (hfsound : ∀ k, Fc (fun j => AbstractDomain.γ (σ j)) k ⊆ AbstractDomain.γ (f k σ)) :
    ∀ k, concreteLfp Fc k ⊆ AbstractDomain.γ (σ k) := by
  have hpf : ∀ k, Fc (fun j => AbstractDomain.γ (σ j)) k ⊆ AbstractDomain.γ (σ k) := by
    intro k a ha
    exact AbstractDomain.γ_monotone _ _ (hpost k) (hfsound k ha)
  intro k cval hc
  exact hc (fun j => AbstractDomain.γ (σ j)) hpf

/--
**The worklist solver is sound.** Specialising `postfixpoint_sound` to `solve`'s
result via `solve_postfixpoint`: a terminating worklist run, over a domain with a
sound transfer, produces a result that over-approximates the concrete collecting
semantics. This is the abstract end-to-end soundness theorem for a worklist
analysis (e.g. sparse constant propagation), modulo instantiating `Fc`/`γ` with the
concrete interpreter semantics.
-/
theorem solve_sound [DecidableEq K] [DecidableEq L] [FiniteHeight L]
    (keys : List K) (hkeys : ∀ k, k ∈ keys) (f : K → (K → L) → L) (enqueue : K → List K)
    (hdep : ∀ (s s' : K → L) (a b : K),
      (∀ j, j ≠ a → s j = s' j) → f b s ≠ f b s' → b ∈ enqueue a)
    (store : K → L) (work : List K)
    (hinv : ∀ k', store k' ⊔ f k' store ≠ store k' → k' ∈ work)
    (Fc : (K → Set Concrete) → K → Set Concrete)
    (hfsound : ∀ k,
      Fc (fun j => AbstractDomain.γ (solve keys hkeys f enqueue store work j)) k
        ⊆ AbstractDomain.γ (f k (solve keys hkeys f enqueue store work))) :
    ∀ k, concreteLfp Fc k ⊆ AbstractDomain.γ (solve keys hkeys f enqueue store work k) :=
  postfixpoint_sound f _ Fc
    (solve_postfixpoint keys hkeys f enqueue hdep store work hinv) hfsound

end Soundness

end MonotoneFramework

end Veir
