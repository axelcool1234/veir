# 3. The sparse dataflow framework — the engineering layer

Files: `Veir/Analysis/DataFlowFramework.lean`, `Veir/Analysis/DataFlow/Facts.lean`,
`Veir/Analysis/DataFlow/SparseFact.lean`, `Veir/Analysis/DataFlow/SparseAnalysis.lean`.

Doc 02 was pure mathematics on an abstract lattice. This layer is the *actual* VeIR
framework: a `HashMap`-backed solver state, a heterogeneous fact store, and the sparse
forward driver that SCCP and dead-code analysis run on. Much of the work here was
**making existing code provable** — several rewrites had no behavioural effect but turned
proof-hostile constructs into proof-friendly ones. This doc explains those decisions,
because they're the kind of thing that looks unmotivated in a diff.

---

## 3.1 The fact store and `DataFlowContext`

`DataFlowFramework.lean` defines the solver state:

```lean
structure DataFlowContext where
  lattice : HashMap LatticeAnchor (DHashMap FactKind Fact)
  registeredAnalyses : HashSet AnalysisKind
  workList : WorkList
```

The `lattice` is the **fact store**: a two-level map from a `LatticeAnchor` (an SSA value,
a CFG edge, or a program point — `Facts.lean`) to a *dependent* map from `FactKind` to the
`Fact` of that kind. It's heterogeneous: dominator facts and constant facts coexist, keyed
by their `FactKind`, with the payload type computed by `FactPayload : FactKind → Type`.

This is the **sparse** structure from doc 01 §1.4: facts live on SSA values, and a
worklist (`WorkList = Queue WorkItem`) drives re-examination.

`FactSpec kind` is the per-kind interface: `mkDefault` (the starting fact, typically `⊥`)
and `propagate` (the hook run when a fact changes, to enqueue dependents).

### Gap (A): lawful keys

To prove *anything* about reading the store after a write you need
`get?`-after-`insert` lemmas for `Std.HashMap`/`DHashMap`, and those require the key types
to be **lawful** — `LawfulBEq` and `LawfulHashable`. `LatticeAnchor` and `CFGEdge`
originally derived only a *structural* `BEq`, which is not lawful.

**Fix:** change them to `deriving DecidableEq` (matching how `ValuePtr` was already done).
The `BEq` derived from `DecidableEq` is lawful by construction (it *is* `decide (a = b)`),
and `LawfulHashable` then follows from `LawfulBEq` via a core instance. Crucially this
needs **nothing** of the components' structure — so we didn't have to make `InsertPoint`
et al. lawful. One-line `deriving` change, unlocks all the store lemmas.

### The keystone lemmas

With lawful keys, `DataFlowFramework.lean` proves the read-after-write facts everything
else is built on:

```lean
@[simp] theorem getFact?_modifyFact_self    : (ctx.modifyFact kind a f).getFact? kind a  = some (f (ctx.getOrMkFact kind a))
         theorem getFact?_modifyFact_of_ne  : a' ≠ a → (ctx.modifyFact kind a f).getFact? kind a' = ctx.getFact? kind a'
         theorem getFact?_congr             : ctx₁.lattice = ctx₂.lattice → ctx₁.getFact? kind a = ctx₂.getFact? kind a
```

and their `…ModifyFactAndPropagate…` variants (parameterized by a hypothesis that
`propagate` leaves the store alone — see §3.2). These are the bridge between the
imperative `HashMap` operations and equational reasoning.

---

## 3.2 `SparseFact.lean`: two proof-driven rewrites

### From `cast` to an isomorphism

The original `SparseFactSpec` asserted a *type equality* `FactPayload kind = SparsePayload Domain`
and used `cast` to move data across it. As warned in doc 01 §1.5, `cast`/`Eq.rec` over data
is poison: it blocks unfolding and forces `cast`-lemma juggling in every proof that touches
a fact.

**Fix:** replace the equality with an explicit **isomorphism plus round-trip laws**:

```lean
class SparseFactSpec (kind) (Domain : outParam Type) where
  toPayload : SparsePayload Domain → FactPayload kind
  ofPayload : FactPayload kind → SparsePayload Domain
  of_to : ∀ p, ofPayload (toPayload p) = p
  to_of : ∀ p, toPayload (ofPayload p) = p
```

When `FactPayload kind` *is* `SparsePayload Domain` (the common case) the instance is
`id`/`id` with `rfl` laws — identical runtime behaviour, zero cast. The payoff: the
round-trip lemmas `getPayload_setPayload` and `latticeElement_setLatticeElement` are now
`@[simp]` lemmas that hold *by the laws*, so `simp` rewrites them away. This is what makes
later soundness proofs (e.g. `joinLatticeElement_extensive`) tractable.

### `propagate` threads the worklist

`propagate` only ever *enqueues* work, but the original threaded the whole `DataFlowContext`
through its loop via `enqueue`, so "propagation doesn't touch the fact store" was true but
not *visible* to the prover. We rewrote it to thread a `WorkList` and apply it once at the
end:

```lean
def propagate (state) (anchor) (dfCtx) (irCtx) := Id.run do
  let mut workList := state.enqueueDependents dfCtx.workList
  …                                    -- only ever: workList := workList.enqueue …
  { dfCtx with workList := workList }   -- store reattached unchanged
```

Now `propagate_preserves_lattice : (propagate …).lattice = dfCtx.lattice` is provable by
`cases anchor <;> rfl`. That lemma is what discharges the `propagate`-leaves-the-store-alone
hypothesis of the `…ModifyFactAndPropagate…` keystones.

---

## 3.3 `SparseAnalysis.lean`: the generic driver and the user's contract

This file is the reusable sparse forward analysis. Three design ideas, each with a "why":

### 1. `SparseForwardSpec` bundles the triple

A sparse analysis is identified by three things that must agree: a `FactKind` (where its
facts live), an `AnalysisKind` (its scheduling tag), and a `Domain` (its lattice). The
original code registered these in three separate places, inviting desync (e.g. passing the
wrong `AnalysisKind` to the constructor). `SparseForwardSpec` makes them one instance:

```lean
class SparseForwardSpec (kind) (Domain : outParam Type) extends SparseFactSpec kind Domain where
  analysisKind : AnalysisKind
```

so `new` reads the tag off the instance — the triple has a single source of truth and
*cannot* desync.

### 2. The transfer is a *pure, domain-level* function: `OpTransfer`

This is the most important design move for verification. The user's analysis used to be an
arbitrary `DataFlowContext → DataFlowContext` function — impossible to state a soundness
spec for. We made it:

```lean
abbrev OpTransfer (Domain : Type) := OperationPtr → IRContext OpCode → Array Domain → Array Domain
```

"given an operation and the *abstract values of its operands*, return the abstract values
of its results." The framework owns *all* the `DataFlowContext` plumbing — reading
operands, deciding when they're ready, subscribing for revisits, joining results back in.
The analysis author writes only `Domain`-level code. Two reasons this matters:

- It keeps the author's code in the **same vocabulary their soundness proof lives in** —
  the abstract domain — instead of HashMap mutation.
- It makes soundness *statable*: `OpTransfer.Sound` (below).

### 3. `joinLatticeElement` and the soundness spec

`joinLatticeElement kind target incoming` is the one primitive that updates a value's fact:
it joins `incoming` into the stored abstraction and propagates on change. Its key proven
property is **extensiveness** — it only ever *raises* a value's abstraction:

```lean
theorem joinLatticeElement_extensive : Extensive (fun dfCtx => joinLatticeElement kind target incoming dfCtx irCtx)
```

(`Extensive` = "never lowers any value's stored abstraction"). This is the concrete
discharge of `MonotoneFramework.Monotone`'s hypothesis for the real driver: the sparse step
climbs the lattice, exactly as the abstract `solve` requires. Its proof is the first place
the keystones (§3.1) and `propagate_preserves_lattice` (§3.2) all come together.

`OpTransfer.Sound` states the per-operation soundness obligation, purely in `γ`/`Domain`
terms (no `DataFlowContext`):

```lean
def OpTransfer.Sound (eval : … concrete op semantics …) (transfer : OpTransfer Domain) : Prop :=
  ∀ op irCtx operandAbs operandConc,
    (∀ i a c, operandAbs[i]? = some a → operandConc[i]? = some c → γ a c) →   -- operands sound
    ∀ i ra rc, (transfer op irCtx operandAbs)[i]? = some ra →
               (eval op operandConc irCtx)[i]? = some rc → γ ra rc            -- results sound
```

`sound_top` proves the trivial all-`⊤` transfer is sound against *any* semantics
(`γ ⊤ = ⊤` does it) — a sanity check that the obligation is dischargeable, not vacuous.

---

## 3.4 The still-`partial` `run`

`run` (in `DataFlowFramework.lean`) is the real worklist loop — dequeue a work item, look
up its analysis, call `visit`, repeat. It is **still `partial def`**. Total-izing it
requires a `potential` over the heterogeneous `HashMap` store (with a per-`FactKind` rank,
including dominance's) plus monotonicity/productivity contracts on the *black-box* `visit`
— the bridge between this layer and the proven `solve` of doc 02. See doc 05 for exactly
why that's a large, separate effort. The abstract model (`solve`) is the proof; `run` is
the unverified-but-executable implementation of it.

Next: the concrete analysis and its soundness against the interpreter —
[04-constant-propagation-and-soundness.md](./04-constant-propagation-and-soundness.md).
