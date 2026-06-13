# Verifying a sparse dataflow framework in Lean

This branch is an experiment in pushing a formal-verification effort as far as
possible: taking VeIR's sparse dataflow analysis framework and proving — in Lean 4,
with **zero `sorry` in `Veir/Analysis`** — that the underlying algorithm terminates,
computes a fixpoint, and is *sound*, and that sparse constant propagation's transfer
function actually agrees with VeIR's interpreter semantics.

It is ~1,300 lines across 11 files. This folder explains what was built, **why**, and
**how it connects to the classical mathematics** of program analysis (lattice theory,
fixed-point theorems, abstract interpretation, the monotone dataflow framework). It is
meant to be read as much as a tutorial as a changelog.

> If you only read one thing: the algorithmic and mathematical *core* is proven
> (`MonotoneFramework.lean`). What is **not** done is bolting that proof onto the
> concrete, `HashMap`-backed, imperative `run` loop — that is an engineering bridge,
> not a missing idea. See [05-status-and-further-reading.md](./05-status-and-further-reading.md).

## How to read this

The documents build up in layers, mirroring the dependency order of the code:

1. **[01-mathematical-background.md](./01-mathematical-background.md)** — the theory
   you need: partial orders and lattices, abstract interpretation and concretization
   (`γ`), the fixed-point theorems (Knaster–Tarski and Kleene), and Kildall's monotone
   dataflow framework. Start here if names like *Kleene iteration* or *Knaster–Tarski*
   are unfamiliar. Includes a curated reading list.
2. **[02-the-monotone-framework.md](./02-the-monotone-framework.md)** — the proven
   abstract engine (`MonotoneFramework.lean`): how `iterateFrom` *is* Kleene iteration,
   how *finite height* makes it terminate, how the worklist solver `solve` is proven
   correct, and how soundness reduces to "a post-fixpoint over-approximates the least
   fixpoint."
3. **[03-the-sparse-dataflow-framework.md](./03-the-sparse-dataflow-framework.md)** —
   the engineering layer (`DataFlowFramework.lean`, `SparseFact.lean`,
   `SparseAnalysis.lean`): the fact store, the design decisions (and a few rewrites we
   did to make the code *provable*), and the lemmas that let us reason about it.
4. **[04-constant-propagation-and-soundness.md](./04-constant-propagation-and-soundness.md)**
   — the concrete analysis (`ConstantDomain.lean`, `SparseConstantPropagationAnalysis.lean`,
   `ConstantSoundness.lean`): the constant lattice, why the transfer function is *not*
   monotone in general (a real finding), and the bridge to the interpreter that proves
   each arithmetic op sound.
5. **[05-status-and-further-reading.md](./05-status-and-further-reading.md)** — exactly
   what is proven vs. deferred, why the remaining gap is hard, and references.
6. **[06-roadblocks-and-blockers.md](./06-roadblocks-and-blockers.md)** — a "here be
   dragons" field guide: the standing blockers (with honest difficulty reads) and a
   catalogue of the smaller traps that actually cost time, each with symptom→fix. Read this
   *before* attempting to finish the proof yourself.
7. **[07-a-field-guide-to-lean-proving.md](./07-a-field-guide-to-lean-proving.md)** — the
   craft: the tactics, strategies, and debugging workflow that moved this proof, plus a
   learning path with deliberately non-obvious resources for doing *complex* Lean proofs.
8. **[08-what-this-proves-and-what-it-doesnt.md](./08-what-this-proves-and-what-it-doesnt.md)**
   — the trust boundary: what the machine actually guarantees (the proofs are `sorry`-free
   and rest only on `propext`/`Quot.sound`), versus what you must still *audit* (the
   definitions and theorem *statements* — where all the residual risk lives). Read this to
   calibrate how much "zero `sorry`" is really worth here.

> Chapters 1–5 are the *what* and *why*; chapters 6–7 are the *how* and the *war stories*;
> chapter 8 is the *how much should I trust this* — arguably the first one to read if you're
> evaluating the artifact rather than extending it.

## File map

| File | What lives there |
|------|------------------|
| `Veir/Analysis/DataFlow/Domains/AbstractDomain.lean` | Order-theory typeclasses (`Top`/`Bot`/`JoinSemilattice`/`BoundedOrder`), the `AbstractDomain` class (concretization `γ` + soundness laws), and `FiniteHeight`. |
| `Veir/Analysis/DataFlow/Domains/ConstantDomain.lean` | The constant lattice `AbstractConstant` (`⊥`/constant/`⊤`), its lattice-law proofs, its `AbstractDomain` and `FiniteHeight` instances. |
| `Veir/Analysis/DataFlow/Domains/LivenessDomain.lean` | The two-point liveness lattice used by dead-code analysis. |
| `Veir/Analysis/DataFlow/MonotoneFramework.lean` | **The proven core.** Kleene iteration (`iterateFrom`), least-fixpoint theorems, the terminating worklist solver (`solve`), and abstract soundness (`solve_sound`). |
| `Veir/Analysis/DataFlowFramework.lean` | The concrete solver state (`DataFlowContext`), the fact store, `FactSpec`, the `getFact?`/`modifyFact` "keystone" lemmas, and the (still `partial`) `run` loop. |
| `Veir/Analysis/DataFlow/Facts.lean` | `LatticeAnchor`, `FactKind`, `Fact`, payloads. |
| `Veir/Analysis/DataFlow/SparseFact.lean` | The sparse fact accessor layer: the payload *isomorphism*, `getElementD`, and `propagate`. |
| `Veir/Analysis/DataFlow/SparseAnalysis.lean` | The generic sparse forward driver: `OpTransfer` (the user's pure transfer), `joinLatticeElement`, the worklist `visit`, and `OpTransfer.Sound`. |
| `Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean` | Sparse constant propagation: the pure `transfer`, the fold helpers, and `transfer_monotone`. |
| `Veir/Analysis/DataFlow/ConstantSoundness.lean` | The interpreter bridge: concretization to `RuntimeValue`, per-op soundness for every arithmetic op, and the end-to-end equation-system soundness theorem. |
| `Veir/Analysis/DataFlow/Soundness.lean` | A "map" file: the value-level soundness predicates and the precise statement of the four gaps (A)–(D) between the abstract proof and the concrete `run`. |

## The one-paragraph summary of the mathematics

A dataflow analysis assigns an *abstract value* (drawn from a lattice `L`) to every
program point, and computes them by repeatedly applying *monotone transfer functions*
until nothing changes — a **fixed point**. The **Knaster–Tarski theorem** guarantees a
*least* fixed point exists for any monotone function on a complete lattice; the
**Kleene fixed-point theorem** says you can *compute* it by iterating from `⊥`
(`⊥, f⊥, f²⊥, …`); and if the lattice has **finite height** (no infinite ascending
chains) that iteration *terminates*. Soundness — the abstract result over-approximates
all real executions — follows because the real ("collecting") semantics is itself the
*least* fixed point of a concrete transfer, and the **concretization** `γ` of a sound
abstract post-fixpoint is a concrete post-fixpoint, hence sits above the least one.
This branch turns every sentence of that paragraph into a checked Lean proof.
