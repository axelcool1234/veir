# 5. Status, the remaining gap, and further reading

## 5.1 What is proven (no `sorry` in `Veir/Analysis`)

The **mathematical and algorithmic core** is complete and machine-checked:

- **Lattice / abstract-domain infrastructure** — `AbstractDomain` (with `γ` and the
  soundness laws), `FiniteHeight`, the `AbstractConstant` lattice and both its
  concretizations.
- **The monotone framework** (`MonotoneFramework.lean`):
  - `iterateFrom` — Kleene iteration as a **total** function (its acceptance *is* the
    termination proof), `iterateFrom_isFixpoint`, `iterateFrom_le_of_fixpoint` (Tarski
    leastness), `iterateFrom_preserves`, and the `lfp_*` wrappers.
  - `solve` — a **total** worklist solver: terminates (`potential` ranking),
    `solve_postfixpoint` (computes a fixed point under a dependency-complete `enqueue`),
    and `solve_sound`/`postfixpoint_sound` (over-approximates the concrete collecting
    semantics `concreteLfp`).
- **Fact-store reasoning** — lawful keys (gap (A), resolved) and the
  `getFact?`/`modifyFact[AndPropagate]` keystone lemmas; `propagate_preserves_lattice`.
- **Sparse driver** — `joinLatticeElement_extensive` (the step climbs the lattice),
  `OpTransfer.Sound` + `sound_top`.
- **Constant propagation** — `transfer_monotone` (on `⊥`-free operands), `foldBinary?_eq`,
  and the **interpreter bridge**: per-op soundness for `constant/addi/muli/subi/andi` vs.
  `LLVM.Int` semantics, assembled into the end-to-end `ConstantPropagation.solve_sound`
  with `constEqn` and `addiEqn`.

In one sentence: **the dataflow algorithm is proven to terminate, compute a fixpoint, and
be sound, and constant propagation's transfer is proven to agree with the real interpreter
— all at the level of a faithful abstract model and an equation system built from that
interpreter.**

## 5.2 What is deferred, and why it's genuinely hard

The single remaining bridge is: **connect the proven abstract `solve` (doc 02) to the
concrete, `HashMap`-backed, `partial` `run` loop** in `DataFlowFramework.lean`. `Soundness.lean`
records this as four gaps:

- **(A) Lawful map keys** — ✅ *resolved* (see doc 03 §3.1).
- **(B) Total-ize `run`.** `run` is `partial`. Making it total needs a `potential` over the
  *heterogeneous, two-level* `HashMap LatticeAnchor (DHashMap FactKind Fact)` store, which
  in turn needs a per-`FactKind` `rank` (including the **dominator** lattice's, a mini
  research problem of its own) and `sum`-after-`insert` reasoning at both map levels. The
  key Std lemma is identified — `Std.HashMap.toList_insert_perm` — so it is *reachable*,
  but it is a large, multi-step development on its own.
- **(C) `visit` contracts.** `run` is generic over an *arbitrary* `visit`; it can only be
  proven terminating/sound if each analysis' `visit` is **extensive** (only raises facts)
  and **productive** (enqueues only on change). The sparse driver's `visit` is a real
  imperative routine (operand subscription, multiple `joinLatticeElement`s, `propagate`
  loops, executability gating); proving *it* decreases the `potential` and preserves the
  soundness invariant is the bulk of the work — and it is **specific to sparse/dead-code**,
  not borrowed from anywhere.
- **(D) The interpreter `eval`.** `OpTransfer.Sound`/`solve_sound` are stated against a
  generic concrete `eval`. The per-op lemmas (doc 04) pin it to `OperationPtr.interpret`
  for the arithmetic, but assembling a single concrete `Fc` from the interpreter for the
  whole store — and the SSA-graph reconstruction that turns each value's defining op into
  its `Eqn` — is more IR plumbing.

> **Important nuance:** deferring dominance does **not** unlock (B)–(D). The obstacle is
> the `HashMap` potential machinery and the imperative driver reasoning *for sparse/dead-code
> themselves*; dominance is an *additional* deferral on top, not the blocker. Honest
> estimate: weeks of Lean, several independent subsystems.

The clean first brick for anyone continuing is the **self-contained `HashMap`
potential-decrease lemma** via `toList_insert_perm` — no dominance, no driver, just the
sum machinery. After that: per-`FactKind` rank, then the driver's `visit` decrease/soundness.

## 5.3 The shape of a "real analysis is correct" proof, for reference

If you come back to extend this, the architecture to aim for (and the one this branch
proves *modulo* the `run` bridge) is the standard verified-abstract-interpreter shape:

```
concrete collecting semantics (= least fixpoint of a concrete transfer)
        ⊆ γ ∘ (abstract least fixpoint)          -- soundness, via post-fixpoint argument
        = γ ∘ (what the worklist computes)       -- algorithm correctness (solve_postfixpoint)
        and the worklist terminates              -- finite height + potential
```

Every arrow above is a theorem we proved abstractly; the open work is showing the concrete
`run` *is* the bottom line of this diagram.

## 5.4 Further reading (curated)

The full list is in [01-mathematical-background.md](./01-mathematical-background.md#reading-list);
the few most relevant to *this branch specifically*:

- **CompCert's `backend/Kildall.v`** (`github.com/AbsInt/CompCert`) — a **fully verified
  generic dataflow (Kildall worklist) solver** in Coq, reused across its constant-propagation,
  liveness, value, and dead-code passes. The single closest relative of
  `MonotoneFramework.solve` + the `run`-bridge: a total, sound worklist over a semilattice,
  with exactly the termination and fixpoint/soundness interface gaps (B)/(C) need. Its
  *fixpoint invariant theorem* is the Coq twin of our `lfp_preserves`/`postfixpoint_sound`
  (doc 02). If you finish the concrete `run`, this is the artifact to imitate.
- **Verasco** — Jourdan, Laporte, Blazy, Leroy, Pichardie, "A formally-verified C static
  analyzer," *POPL 2015*. The closest existing *abstract-interpreter* artifact: a complete
  verified AI in Coq. Its soundness architecture (concretization, post-fixpoint soundness,
  fixpoint iteration **with widening**) is the same one this branch builds — minus widening,
  which it needs because its domains are infinite-height and ours aren't (doc 07 §7.7).
- For the abstract-interpretation *theory* you'd build on (Galois connections, widening):
  **Rival & Yi, *Introduction to Static Analysis*** and **Cousot, *Principles of Abstract
  Interpretation*** (full list in doc 01).
- **Nielson, Nielson & Hankin, *Principles of Program Analysis*** — the textbook for the
  monotone framework, worklist algorithms, and the lattice/fixpoint background.
- **Tarski (1955)** and the **Kleene fixed-point theorem** (Wikipedia is fine) — the two
  theorems doc 02 mechanizes.
- **Cousot & Cousot, *POPL 1977*** — abstract interpretation's founding paper (read a
  tutorial first).
- **MLIR DataFlow analysis docs** (`mlir.llvm.org`) — the concrete framework design VeIR's
  mirrors (lattice anchors, sparse forward analyses).
- **Wegman & Zadeck, *TOPLAS 1991*** — SCCP, the analysis verified in doc 04.
- ***Theorem Proving in Lean 4*** — for `termination_by`/`decreasing_by` and well-founded
  recursion, the machinery that makes `iterateFrom`/`solve` total.

## 5.5 A note on the experiment

This branch was an experiment in how far an AI agent could carry a non-trivial Lean
verification. The arc it actually traversed, in order, was: simplify the framework's API
(the `cast`→iso rewrite, the `OpTransfer` redesign) → build the abstract monotone-framework
engine (Kleene + worklist, termination + fixpoint + soundness) → make the concrete fact
store provable (lawful keys + keystones) → bridge to the interpreter (per-op soundness) →
assemble the end-to-end equation-model soundness theorem. The recurring lesson, visible all
over the diff, is that **most of the work in mechanized verification is making code
*provable*** — replacing `cast` with isomorphisms, `partial` with well-founded recursion,
black-box transfers with pure domain-level functions — not the final proofs themselves.
