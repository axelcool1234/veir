# 1. Mathematical background

This document is the theory primer. It explains the concepts the proofs rest on, in
roughly the order you meet them in the code. If you already know lattice theory,
abstract interpretation, and fixed-point theorems, skim to the [reading list](#reading-list)
and move on to [02-the-monotone-framework.md](./02-the-monotone-framework.md).

---

## 1.1 Partial orders and lattices

A **partial order** `(L, ≤)` is a set with a reflexive, transitive, antisymmetric
relation. In analysis the order means *information precision*: `a ≤ b` reads "`a` is at
least as precise as `b`" (equivalently, "`b` over-approximates `a`").

A **join-semilattice** additionally has, for every pair `a, b`, a *least upper bound*
`a ⊔ b` (the **join**) — the most precise value that over-approximates both. The join
is what an analysis uses to *merge* information arriving from two control-flow paths.

Two distinguished elements matter:

- **`⊥` (bottom)** — the most precise / "no information yet" element (`⊥ ≤ x` for all
  `x`). Analyses start here.
- **`⊤` (top)** — the least precise / "could be anything" element (`x ≤ ⊤` for all `x`).
  Analyses fall back to it when they give up.

A lattice with both is a **bounded lattice**.

> **In the code.** `AbstractDomain.lean` defines these as small typeclasses:
> `Top`, `Bot`, `OrderTop`, `OrderBot`, `BoundedOrder`, `Join`, and `JoinSemilattice`
> (which bundles the partial-order laws `le_refl`/`le_trans`/`le_antisymm` with the
> three join laws `le_join_left`, `le_join_right`, `join_le`). We deliberately did *not*
> pull in Mathlib's order hierarchy — VeIR doesn't depend on Mathlib — so these are
> hand-rolled and minimal.

### Finite height (the Ascending Chain Condition)

A lattice satisfies the **Ascending Chain Condition (ACC)** if it has no infinite
strictly-increasing chain `a₀ < a₁ < a₂ < …`. A lattice has **finite height** if every
chain is bounded by a fixed length. Finite height ⟹ ACC, and ACC is exactly what makes
iterative fixpoint computation *terminate*: you can only climb so far before you must
stop.

> **In the code.** `FiniteHeight` (in `AbstractDomain.lean`) encodes this as a *measure*:
> a function `rank : α → Nat` that strictly increases along the order
> (`a ≤ b → a ≠ b → rank a < rank b`) together with a uniform bound `maxRank`. This
> "ACC in measure form" is precisely what a well-founded termination argument needs.
> The constant lattice has height 3 (`⊥ < constant < ⊤`), so `rank` is `0/1/2`.

---

## 1.2 Abstract interpretation and concretization

**Abstract interpretation** (Cousot & Cousot, 1977) is the general theory of *sound
approximation* of program semantics. The setup:

- A **concrete domain** of "what really happens" — e.g. *sets of concrete values* a
  variable can take, ordered by `⊆`.
- An **abstract domain** `L` of *finite descriptions* — e.g. `⊥ / a constant / ⊤`.
- A **concretization function** `γ : L → ℘(Concrete)` mapping each abstract value to the
  set of concrete values it denotes. `γ ⊤ = everything`, `γ ⊥ = ∅`, and crucially `γ`
  is **monotone**: `a ≤ b → γ a ⊆ γ b` (a less precise abstract value denotes a larger
  set). Many treatments also use an **abstraction** `α` forming a *Galois connection*
  `α ⊣ γ`; we only ever needed `γ`, the "γ-only" or *soundness-relation* presentation,
  which is lighter and sufficient for proving over-approximation.

**Soundness** of an analysis means: for every program point, every value that can
*actually* occur there is in the `γ` of the computed abstract value. The abstract value
*over-approximates* reality. (It may be imprecise — `⊤` is always sound — but it never
lies by omission.)

> **In the code.** `AbstractDomain AbstractValue ConcreteValue` (in `AbstractDomain.lean`)
> is the class carrying `γ` and its three laws: `γ_top`, `γ_bot`, `γ_monotone`. The
> constant domain has *two* instances: `AbstractDomain AbstractConstant ConcreteConstant`
> (pure math) and `AbstractDomain AbstractConstant RuntimeValue` (the bridge to the
> interpreter's actual values; see doc 04).

---

## 1.3 Fixed points: Knaster–Tarski and Kleene

A **fixed point** of `f` is an `x` with `f x = x`. A **pre-fixpoint** has `x ≤ f x`; a
**post-fixpoint** has `f x ≤ x`. These are the heart of dataflow analysis: the answer
we want is a fixed point of the system of transfer functions.

### The Knaster–Tarski theorem (1928 / 1955)

> *Every monotone function `f` on a complete lattice has a complete lattice of fixed
> points. In particular it has a least fixed point*
> `lfp f = ⊓ { x | f x ≤ x }` *— the meet (greatest lower bound) of all its
> post-fixpoints.*

Two consequences we use constantly:

1. **`lfp f` exists** for monotone `f` (no continuity needed).
2. **`lfp f` is the *least* post-fixpoint**: if `f x ≤ x` then `lfp f ≤ x`. This is the
   engine of soundness proofs (sometimes called **Park induction**): to show
   `lfp f ≤ x`, just show `x` is a post-fixpoint.

The least-post-fixpoint characterization is what makes our soundness proof a *two-liner*
once set up: the concrete collecting semantics is `lfp` of a concrete transfer, the
concretization `γ ∘ σ` of a sound abstract result is a concrete *post-fixpoint*, so the
collecting semantics ≤ `γ ∘ σ` — i.e. every real value is captured. See `postfixpoint_sound`
in doc 02.

### The Kleene fixed-point theorem

Knaster–Tarski says `lfp` *exists* but not how to *compute* it. **Kleene's theorem**
does:

> *For a Scott-continuous `f` on a pointed CPO, `lfp f = ⊔ₙ fⁿ(⊥)` — the supremum of the
> ascending **Kleene chain*** `⊥ ≤ f⊥ ≤ f²⊥ ≤ f³⊥ ≤ …`.

So you compute the least fixed point by *iterating from `⊥`*. In general this is an
infinite supremum, but:

> **If the lattice has finite height (ACC), the Kleene chain stabilizes after finitely
> many steps** — `fⁿ⁺¹(⊥) = fⁿ(⊥)` for some finite `n` — and that stable value *is*
> `lfp f`.

This is the precise reason iterative dataflow analysis works on finite-height lattices,
and it is exactly what `iterateFrom` in `MonotoneFramework.lean` implements and proves
terminating (doc 02).

---

## 1.4 The monotone dataflow framework (Kildall, 1973)

Kildall unified dataflow analyses into one schema:

- Pick a lattice `L` of "facts."
- Attach a fact to each program point.
- Give each instruction a **monotone transfer function** describing how it transforms
  facts.
- The solution is the fixed point of the resulting system of equations, computed by
  iteration to convergence. The classic **MFP** ("maximal fixed point" — really the
  least, depending on `⊥`/`⊤` orientation) solution is what a worklist algorithm
  computes.

**Sparse** dataflow analysis (e.g. the framework in MLIR, and SCCP below) specializes
this: instead of a fact per program *point*, it keeps a fact per **SSA value**, and only
re-examines a value's *users* when its fact changes — driven by a **worklist**. That is
the structure of `DataFlowFramework.run` and the `SparseAnalysis` driver (doc 03), and
its abstract model is `solve` (doc 02).

**Sparse Conditional Constant Propagation (SCCP)** (Wegman & Zadeck, 1991) is the
flagship sparse analysis and our running example: it propagates constants through SSA,
simultaneously tracking which branches are executable.

---

## 1.5 Why we needed a custom termination/soundness proof at all

Two practical wrinkles drove much of the engineering:

- **`partial` is opaque.** Lean's `partial def` (used for the real `run` loop, which
  *might* loop forever for a misbehaving analysis) is invisible to the logic — you
  cannot prove anything by induction on it. To reason about termination you must either
  re-express the loop as **well-founded recursion** with a decreasing measure, or prove
  the result via a separate model. We did the latter for the algorithm (`solve`).
- **`cast` is poison for proofs.** Transporting data across a *type equality* with `cast`
  / `Eq.rec` blocks definitional unfolding and forces painful `cast`-juggling in every
  downstream proof. We replaced one such `cast` with an explicit *isomorphism + round-trip
  laws* (doc 03), which `simp` handles for free.

Both are recurring themes; the docs flag them where they appear.

---

## Reading list

Accessible entry points first, classics after.

**Fixed-point theory**
- *Knaster–Tarski theorem* — Wikipedia, "Knaster–Tarski theorem," is a good first read.
  Original: A. Tarski, "A lattice-theoretical fixpoint theorem and its applications,"
  *Pacific J. Math.* 5 (1955).
- *Kleene fixed-point theorem* — Wikipedia, "Kleene fixed-point theorem."
- Davey & Priestley, *Introduction to Lattices and Order* (2002) — the standard gentle
  textbook for everything in §1.1 and §1.3.

**Abstract interpretation**
- A. Møller & M. Schwartzbach, *Static Program Analysis* (`cs.au.dk/~amoeller/spa/`, free,
  regularly-updated lecture notes) — the best *free* on-ramp: lattices, the monotone
  framework, the worklist algorithm, then widening and abstract interpretation. Closest to
  what docs 01–02 formalize, presented gently. Start here.
- X. Rival & K. Yi, *Introduction to Static Analysis: An Abstract Interpretation
  Perspective* (MIT Press, 2020) — the accessible modern textbook: Galois connections,
  domain design, widening/narrowing, worked domains.
- P. Cousot, *Principles of Abstract Interpretation* (MIT Press, 2021) — the definitive,
  comprehensive treatment by the field's founder. Dense; grow into it.
- P. Cousot & R. Cousot, "Abstract interpretation: a unified lattice model…," *POPL 1977*
  — the founding paper (dense; read a survey first).
- For the `γ`-only ("soundness relation") style we use, see any treatment of
  *concretization-based soundness* — e.g. the relevant chapters of the *Software
  Foundations*-adjacent course "Verified Static Analysis" / "Abstract Interpretation in
  Coq" materials (Jourdan, Pichardie et al.).

> **Note on widening.** All of the above devote serious space to **widening/narrowing**,
> which this branch *does not use* — we get termination from *finite height* (the ACC)
> instead. For any infinite-height domain (intervals, polyhedra) widening is mandatory; see
> doc 07 §7.7 for why and how to learn it.

**Dataflow analysis**
- G. Kildall, "A unified approach to global program optimization," *POPL 1973* — the
  monotone framework.
- M. Wegman & F. K. Zadeck, "Constant propagation with conditional branches," *TOPLAS
  1991* — SCCP.
- Nielson, Nielson & Hankin, *Principles of Program Analysis* (1999) — the comprehensive
  textbook; chapters on the monotone framework and worklist algorithms.
- The MLIR "DataFlow analysis" docs (`mlir.llvm.org`) — the concrete framework VeIR's is
  modeled on (sparse forward analyses, lattice anchors, etc.).

**Mechanized verification (closest in spirit to this branch)**
- J.-H. Jourdan, V. Laporte, S. Blazy, X. Leroy, D. Pichardie, "A formally-verified C
  static analyzer," *POPL 2015* (the Verasco project) — a full verified abstract
  interpreter in Coq; the soundness architecture mirrors ours (concretization,
  post-fixpoint soundness, fixpoint iteration with widening).
- The CompCert project (Leroy et al.) for the surrounding verified-compiler context.

**Lean-specific**
- *Theorem Proving in Lean 4* (leanprover.github.io) — for the tactic and well-founded
  recursion machinery (`termination_by`, `decreasing_by`) used throughout doc 02.
