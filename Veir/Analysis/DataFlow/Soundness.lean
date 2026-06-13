module

public import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis
public import Veir.Analysis.DataFlow.MonotoneFramework

public section

namespace Veir

namespace DataFlowSoundness

/-!
# Connecting the monotone-framework engine to the concrete solver

`MonotoneFramework` proves, abstractly, that a monotone function on a
finite-height lattice has a least fixpoint reachable by terminating iteration,
and that any `f`-closed predicate (e.g. γ-soundness) transports to it. This file
records the obligations that connect that engine to the concrete worklist solver
(`run`) and the sparse analyses, and discharges the ones that need no further
infrastructure.

There are four infrastructure gaps between here and a fully-verified `run`; each
is called out at the relevant obligation below:

* **(A) Lawful map keys + step keystones.** ✅ *Resolved.* `LatticeAnchor` (and
  `CFGEdge`) derive `DecidableEq`, supplying the lawful `BEq`/`LawfulBEq`/
  `LawfulHashable` used as the fact-store key. On top of this,
  `DataFlowContext.getFact?_modifyFact_self`/`_of_ne` and their
  `…ModifyFactAndPropagate…` variants (in `DataFlowFramework.lean`) are proven, and
  `SparseFact.propagate_preserves_lattice` discharges the propagate side. Together
  these prove `joinLatticeElement_extensive` below — the sparse step is monotone on
  the fact store.
* **(B) Worklist termination + fixpoint + soundness.** The *abstract* worklist
  solver `MonotoneFramework.solve` is a **total** (non-`partial`) definition: it
  terminates by the lexicographic measure `(potential keys store, work.length)`,
  proven from finite height (`potential_update_lt`). `solve_postfixpoint` proves its
  result satisfies the dataflow equations (`∀ k, f k result ≤ result k`) given a
  dependency-complete `enqueue`, and `solve_sound` proves the result
  over-approximates the concrete collecting semantics (`concreteLfp`) when the
  transfer soundly abstracts it — so the worklist discipline is fully correct:
  it terminates, reaches a fixpoint, *and* is sound. This is the model
  `DataFlowFramework.run` implements. Transferring it to the concrete `run` still needs a `rank`/`maxRank`
  on every `FactKind` (so `FactSpec` can expose one) and a `potential` summed over
  the heterogeneous `HashMap` fact store — `Std.HashMap` lacks a
  `sum`/`fold`-after-`insert` lemma, so that sum is the remaining work.
* **(C) `visit` contracts.** `run` is generic over an arbitrary `visit`; it can
  only terminate / stay sound if each analysis' `visit` is *extensive* (only
  raises facts) and *productive* (enqueues only on change). Dominance and the
  sparse driver both satisfy these, but it must be proven.
* **(D) The concrete semantics bridge.** `OpTransfer.Sound` is stated against an
  abstract `eval`; making it bite needs `eval := OperationPtr.interpret` with a
  concretization relating the interpreter's `RuntimeValue`s to the domain's
  `Concrete`.
-/

open SparseForwardDataFlowAnalysis

/-! ## Item 2: step contracts (definitions are complete; discharge is gated on (A)) -/

variable {Domain : Type} {kind : FactKind}

/--
A context-to-context step is **extensive** for the sparse fact slot `kind` when
it never lowers any value's stored abstraction. This is the monotonicity
contract a sparse `visit` must satisfy for `run` to terminate (climbing a
finite-height lattice) and to compute the least fixpoint.
-/
def Extensive [SparseFactSpec kind Domain] [FactSpec kind] [LE Domain] [Bot Domain]
    (step : DataFlowContext → DataFlowContext) : Prop :=
  ∀ (dfCtx : DataFlowContext) (v : ValuePtr),
    SparseFact.getElementD kind v ⊥ dfCtx ≤ SparseFact.getElementD kind v ⊥ (step dfCtx)

/--
`joinLatticeElement` is extensive: joining only raises the target's abstraction
(and leaves every other value untouched). **Proven.**

The proof assembles the keystones: `joinLatticeElement` is a
`modifyFactAndPropagate`, whose store equals the corresponding `modifyFact`
because `SparseFact.propagate` preserves `.lattice`
(`getFact?_modifyFactAndPropagate_self`/`_of_ne` discharge that with
`propagate_preserves_lattice`). At the target the new element is `old ⊔ incoming ≥
old` (`le_join_left`); elsewhere the fact is unchanged.
-/
theorem joinLatticeElement_extensive
    [SparseFactSpec kind Domain]
    [LE Domain] [Bot Domain] [DecidableEq Domain] [JoinSemilattice Domain]
    (target : ValuePtr) (incoming : Domain) (irCtx : IRContext OpCode) :
    Extensive (kind := kind) (fun dfCtx => joinLatticeElement kind target incoming dfCtx irCtx) := by
  intro dfCtx v
  have hprop : ∀ (s : Fact kind) (c : DataFlowContext),
      (s.propagate (.ValuePtr target) c irCtx).lattice = c.lattice :=
    fun s c => SparseFact.propagate_preserves_lattice s (.ValuePtr target) c irCtx
  show SparseFact.getElementD kind v ⊥ dfCtx
    ≤ SparseFact.getElementD kind v ⊥ (joinLatticeElement kind target incoming dfCtx irCtx)
  simp only [SparseForwardDataFlowAnalysis.joinLatticeElement, Id.run]
  split
  · -- no change: result is `dfCtx`
    exact Std.IsPreorder.le_refl _
  · -- changed: result is a `modifyFactAndPropagate` at `.ValuePtr target`
    by_cases hv : v = target
    · subst hv
      rw [SparseFact.getElementD_of_getFact? kind v ⊥ _ _
            (DataFlowContext.getFact?_modifyFactAndPropagate_self kind dfCtx (.ValuePtr v) _ irCtx hprop),
          SparseFact.latticeElement_setLatticeElement]
      exact JoinSemilattice.le_join_left _ _
    · rw [SparseFact.getElementD_congr kind v ⊥
            (DataFlowContext.getFact?_modifyFactAndPropagate_of_ne kind dfCtx _ irCtx hprop
              (by simpa using hv))]
      exact Std.IsPreorder.le_refl _

/-! ## Item 3: value-level γ-soundness (definition complete; transport via the engine) -/

variable {Concrete : Type}

/--
The stored facts of slot `kind` are **sound** with respect to a concrete
"reaches" relation when every value `v` that concretely takes `c` has `c` in the
concretization of `v`'s stored abstraction. This is `MonotoneFramework`'s
soundness predicate `P`, specialized to the value lattice and lifted over the
whole context.
-/
def SoundValue [SparseFactSpec kind Domain] [FactSpec kind] [LE Domain] [Bot Domain]
    [AbstractDomain Domain Concrete]
    (reaches : ValuePtr → Concrete → Prop) (dfCtx : DataFlowContext) : Prop :=
  ∀ (v : ValuePtr) (c : Concrete),
    reaches v c → AbstractDomain.γ (SparseFact.getElementD kind v ⊥ dfCtx) c

/--
**Item 1 + 2 + 3 connection.** Under the analysis `visit` contracts (C), once
`run` is re-expressed as well-founded recursion over the potential (B) using
lawful keys (A), `run` returns a context that is both a fixpoint of the step and
sound (D, via `MonotoneFramework.lfp_preserves`).

This is the top-level theorem the whole effort targets; its proof is the
composition of the four gaps above and is left open here.
-/
theorem run_sound_fixpoint : True := by trivial

end DataFlowSoundness

/-! ## Item 2 (self-contained): the sparse-constant transfer is monotone

`SparseConstantPropagation.transfer_monotone` (in
`SparseConstantPropagationAnalysis.lean`, beside the `transfer` definition it
unfolds) proves that the constant-propagation transfer is monotone on `⊥`-free,
equal-arity operands. The `⊥`-freeness is *essential* — `transfer` is **not**
monotone in general: with operands `#[⊥, ⊥] ≤ #[constant c, constant d]`,
`arith.addi` cannot fold through `⊥` so it returns `⊤`, but folds the larger
operands to `constant (c + d)`, and `⊤ ≰ constant (c + d)`. The driver's
"wait until every operand is initialized" guard is exactly what restricts
`transfer` to the sub-lattice where it is monotone — so the monotone step the
framework iterates is the *guarded* driver step, not the raw `transfer`. -/

end Veir
