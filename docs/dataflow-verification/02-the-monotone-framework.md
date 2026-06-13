# 2. The monotone framework — the proven core

File: `Veir/Analysis/DataFlow/MonotoneFramework.lean` (~390 lines).

This is the mathematical heart of the branch and the part with **no `sorry`**. It proves,
abstractly and reusably, that monotone fixpoint computation on a finite-height lattice
**terminates**, **computes the least fixed point**, and **transports soundness**. Then it
proves the same three things for a **worklist** solver — the algorithm an actual sparse
analysis runs.

Everything here is generic over a lattice `α` (or `L`); none of it knows about VeIR IR.
That separation is deliberate: the messy, IR-specific code (doc 03) only has to show it
*instantiates* this engine.

---

## 2.1 Kleene iteration: `iterateFrom`

Recall from doc 01 that for a monotone `f` on a finite-height lattice,
`lfp f = fⁿ(⊥)` for some finite `n`, found by iterating from `⊥` until the value stops
changing. That is *exactly* this definition:

```lean
def iterateFrom (f : α → α) (hf : Monotone f) : (x : α) → x ≤ f x → α
  | x, hx => if h : f x = x then x else iterateFrom f hf (f x) (hf hx)
termination_by x => FiniteHeight.maxRank (α := α) - FiniteHeight.rank x
decreasing_by …
```

Read it as: "if applying `f` changes nothing, you're at the fixed point — return it;
otherwise step to `f x` and recurse." `Monotone f` is `∀ a b, a ≤ b → f a ≤ f b`, and the
`x ≤ f x` argument is the invariant that we are climbing the Kleene chain (it's preserved
because `f` is monotone).

**The crucial point: this is *not* a `partial def`.** Lean only accepts it because the
recursion is *well-founded*, and the proof obligation is discharged by `decreasing_by`
using finite height: each real step strictly raises `rank`, and `rank` is capped by
`maxRank`, so the measure `maxRank − rank x` strictly decreases. **The fact that the
definition elaborates at all *is* the termination theorem.** This is Kleene's theorem
specialized to ACC lattices, made executable.

`lfp f := iterateFrom f hf ⊥ (bot_le …)` starts the chain at `⊥`.

> Why `maxRank − rank` and not just `rank`? We need a *decreasing* `Nat` measure for
> well-founded recursion; `rank` *increases*, so we subtract it from its bound. This is
> the standard "remaining capacity" trick.

### What's proven about it

| Lemma | Meaning | Maths |
|-------|---------|-------|
| `iterateFrom_isFixpoint` | the result `r` satisfies `f r = r` | the Kleene chain stabilizes at a fixed point |
| `iterateFrom_le_of_fixpoint` | `r ≤ p` for any fixed point `p ≥` the start | leastness (Knaster–Tarski / Park) |
| `iterateFrom_preserves` | any predicate `P` with `P x → P (f x)`, true at the start, holds at `r` | invariant transport — the soundness engine |
| `lfp_isFixpoint`, `lfp_least`, `lfp_preserves` | the same, specialized to `lfp f` (start `⊥`) | |

`lfp_preserves` is the abstract soundness theorem in miniature: if your soundness
property survives one step of `f` and holds at `⊥`, it holds at the least fixed point.
That is the inductive backbone of *every* "the analysis result is sound" argument.

> **Proof-engineering note.** These were proved with the auto-generated `iterateFrom.induct`
> principle (Lean derives an induction principle for well-founded definitions) rather than
> by re-deriving the recursion in tactic mode — the latter doesn't give `decreasing_by`
> access to the right hypotheses. The base case needed `simp only [iterateFrom]` to fire
> the per-pattern equation lemma; defeq alone won't unfold a WF definition.

---

## 2.2 The worklist solver: `solve`

`iterateFrom` re-applies `f` to the *whole* state each round — correct but wasteful. A
real analysis keeps a **worklist** of keys still to (re)compute and only revisits a key's
*dependents* when its value changes. That is `DataFlowFramework.run` in the wild; here is
its verified abstract model:

```lean
def solve [LE L] [DecidableEq L] [JoinSemilattice L] [FiniteHeight L]
    (keys : List K) (hkeys : ∀ k, k ∈ keys)
    (f : K → (K → L) → L) (enqueue : K → List K) :
    (K → L) → List K → (K → L)
  | store, [] => store
  | store, k :: rest =>
    if store k ⊔ f k store = store k then
      solve keys hkeys f enqueue store rest                       -- no change: drop k
    else
      solve keys hkeys f enqueue (update store k (store k ⊔ f k store)) (rest ++ enqueue k)
termination_by store work => (potential keys store, work.length)
```

The state is a `store : K → L` (one lattice value per key). Pop a key `k`; recompute its
value `f k store`; join it in. If nothing rose, drop `k`; if it rose, write the new value
and **re-enqueue `k`'s dependents** (`enqueue k`).

### Termination: the potential function

The measure is **lexicographic**, `(potential keys store, work.length)`:

```lean
def potential (keys : List K) (store : K → L) : Nat :=
  (keys.map (fun k => FiniteHeight.maxRank (α := L) - FiniteHeight.rank (store k))).sum
```

`potential` is the **total remaining climb** — summed over all keys, how much higher each
value could still go. The termination argument is the classic worklist one:

- A **productive** step (a value strictly rises) **lowers `potential`** — proved in
  `potential_update_lt` (one key's `maxRank − rank` term strictly drops, the rest are
  unchanged; `sumMap_lt` does the list-sum bookkeeping).
- An **unproductive** step (no change) keeps `potential` fixed but **shortens the
  worklist**.

So `(potential, |worklist|)` strictly decreases under the lexicographic order every step.
Finite height bounds `potential`, so the loop halts. Again: `solve` is a **total**
definition — Lean accepting it is the termination proof, no fuel, no `partial`.

`hkeys : ∀ k, k ∈ keys` says `keys` enumerates every key (needed so a productive update
to *any* key actually appears in the `potential` sum). `join_absorb` (`(a ⊔ b) ⊔ b = a ⊔ b`)
is a small lattice lemma used to show the updated key itself settles.

### Correctness: `solve_postfixpoint`

Termination alone isn't enough — does `solve` reach a real fixed point?

```lean
theorem solve_postfixpoint … (hdep : dependency-complete enqueue) :
    ∀ store work, (worklist covers every currently-violated key) →
      ∀ k, f k (solve … store work) ≤ (solve … store work) k
```

i.e. on return, **every key satisfies its dataflow equation** `f k result ≤ result k`
(it's a *post-fixpoint* of the system — no further progress possible). The proof carries
the **worklist invariant** "every key whose equation is currently violated is on the
worklist." Preserving it across a productive step is exactly where `enqueue` must be
**dependency-complete** (`hdep`):

```lean
hdep : ∀ s s' a b, (∀ j, j ≠ a → s j = s' j) → f b s ≠ f b s' → b ∈ enqueue a
```

"if changing the store at `a` could change `f b`, then `b ∈ enqueue a`." This is precisely
the contract a real "re-enqueue this fact's dependents on change" routine must satisfy —
now made explicit and *required* for the correctness theorem. When the worklist empties,
the invariant says no key is violated, so the equations hold everywhere.

---

## 2.3 Soundness: post-fixpoints over-approximate reality

This is where doc 01's *least-post-fixpoint* idea pays off. We model the **concrete
collecting semantics** as the least fixed point of a concrete transfer `Fc` over
`K → Set Concrete`:

```lean
def concreteLfp (Fc : (K → Set Concrete) → K → Set Concrete) : K → Set Concrete :=
  fun k cval => ∀ y, (∀ j, Fc y j ⊆ y j) → cval ∈ y k
```

This is literally "the intersection of all `Fc`-closed concrete stores" = the *least*
post-fixpoint of `Fc`. Defining it this way makes **leastness definitional** — we get
"`concreteLfp Fc ⊆ y` for any post-fixpoint `y`" for free, with **no complete-lattice
Knaster–Tarski machinery to build**. (We don't even need `Fc` monotone, because we only
use the leastness direction.)

```lean
theorem postfixpoint_sound (f σ Fc)
    (hpost : ∀ k, f k σ ≤ σ k)                                   -- σ is an abstract post-fixpoint
    (hfsound : ∀ k, Fc (γ ∘ σ) k ⊆ γ (f k σ)) :                 -- f soundly abstracts Fc at σ
    ∀ k, concreteLfp Fc k ⊆ γ (σ k)
```

The proof is the textbook argument in three lines:

1. `γ ∘ σ` is a **concrete post-fixpoint** of `Fc`: `Fc (γ∘σ) k ⊆ γ (f k σ) ⊆ γ (σ k)`,
   using `hfsound` then `γ_monotone` on the abstract post-fixpoint `hpost`.
2. `concreteLfp Fc` is the *least* post-fixpoint, so it sits below `γ ∘ σ`.
3. Therefore every concrete value a key can take lies in `γ (σ k)` — **soundness**.

`solve_sound` simply chains `solve_postfixpoint` (which produces the abstract post-fixpoint
`hpost`) into `postfixpoint_sound`:

```lean
theorem solve_sound … (Fc) (hfsound : … the result …) :
    ∀ k, concreteLfp Fc k ⊆ γ (solve … k)
```

> **Read this as the capstone of the abstract layer:** a terminating worklist run, over a
> finite-height domain whose transfer soundly abstracts the concrete semantics, produces a
> result that over-approximates every real execution. Termination + fixpoint + soundness,
> all proven, all reusable.

---

## 2.4 How the pieces map to the theorems

| Mathematical statement | Lean name |
|---|---|
| ACC / finite height | `FiniteHeight` (`rank`, `maxRank`, `rank_lt_of_lt`) |
| Kleene iteration computes a fixed point | `iterateFrom` + `iterateFrom_isFixpoint` |
| Knaster–Tarski leastness (Park induction) | `iterateFrom_le_of_fixpoint`, `lfp_least` |
| Invariant transport through the iteration | `iterateFrom_preserves`, `lfp_preserves` |
| Worklist terminates (ranking function) | `solve` + `potential` + `potential_update_lt` |
| Worklist computes the MFP solution | `solve_postfixpoint` (with `hdep`) |
| Collecting semantics = least concrete post-fixpoint | `concreteLfp` |
| Sound post-fixpoint over-approximates collecting semantics | `postfixpoint_sound`, `solve_sound` |

Next: how the concrete, IR-facing framework is built and made provable —
[03-the-sparse-dataflow-framework.md](./03-the-sparse-dataflow-framework.md).
