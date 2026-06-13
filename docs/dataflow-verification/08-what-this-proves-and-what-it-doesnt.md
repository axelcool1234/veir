# 8. What this proves — and what it doesn't (the trust boundary)

"Zero `sorry`" is easy to over-read. This chapter draws the precise line between **what is
mechanically guaranteed** and **what you still have to take on faith (or audit yourself)**.
For a verification artifact — *especially* one generated largely by an AI — this is the most
important chapter, because the kernel checks your *proofs*, not whether you stated the
*right theorems*.

---

## 8.1 What the machine actually guarantees

Lean's trusted kernel re-checks every proof term. So for every theorem in this branch, the
claim "the conclusion follows from the hypotheses and definitions" is checked at the
foundations, modulo a tiny, well-understood axiom base. We verified that base:

```
#print axioms Veir.MonotoneFramework.solve_sound
  -- depends on axioms: [propext, Quot.sound]
#print axioms Veir.ConstantPropagation.solve_sound
  -- depends on axioms: [propext, Quot.sound]
#print axioms Veir.MonotoneFramework.postfixpoint_sound
  -- does not depend on any axioms
```

- **`propext`** (propositional extensionality) and **`Quot.sound`** (soundness of quotients)
  are two of Lean's three standard, universally-trusted axioms. Their presence is routine —
  essentially every Lean development uses them.
- Notably **`Classical.choice` is *absent*** — these proofs are constructive (the third
  standard axiom isn't needed), and `postfixpoint_sound` uses **no axioms at all**.
- A scan of the changed files finds **no `sorry`, no `axiom`, no `native_decide`, no
  `unsafe`, no `@[implemented_by]`/`@[extern]`** in `Veir/Analysis`. There are no escape
  hatches; the proofs are honest all the way down.

So the *proof* side is as trustworthy as Lean gets. **All the residual risk is on the
*statement* side.**

---

## 8.2 The real question: do the statements say what you want?

A machine-checked proof of the *wrong theorem* is worthless. Two failure modes to guard
against, both about **definitions and theorem statements**, not proofs:

1. **Vacuity.** A theorem with an unsatisfiable hypothesis, or a trivial conclusion, is
   "true" and useless. (Classic example: a soundness theorem quantified over an abstract
   `eval` you never instantiate proves nothing about the *real* semantics.)
2. **Misencoding.** A definition that *looks* like the intended concept but isn't (a `γ`
   that's too permissive, a "collecting semantics" that doesn't model real executions, a
   transfer that silently ignores a case).

The kernel will not catch either. *You* have to, by reading the **definitions** — they are
the axioms of your specification. Below is the audit list.

---

## 8.3 Audit checklist — the definitions that *encode* "correct"

These are the load-bearing specifications. If any of them is wrong, a green build proves the
wrong thing. Scrutinize them in roughly this priority order.

| Definition | Where | What it claims to mean | What to check / how it could be wrong |
|---|---|---|---|
| `AbstractDomain.γ` + `γ_top`/`γ_bot`/`γ_monotone` | `AbstractDomain.lean` | concretization: which concrete values an abstract value denotes | Is `γ` faithful? A `γ` that's *too large* makes soundness trivially true but precision claims hollow; `γ ⊥ = ∅`, `γ ⊤ = everything` are the sanity checks (proved as `γ_bot`/`γ_top`). |
| `AbstractConstant.γRuntime` | `ConstantSoundness.lean` | a constant denotes exactly the matching interpreter `RuntimeValue` | This is the bridge to *reality*. Check it really pins `.int bw v` and nothing else; a sloppy version (e.g. ignoring bitwidth) would make per-op "soundness" meaningless. |
| `concreteLfp` | `MonotoneFramework.lean` | the concrete collecting semantics = least post-fixpoint of `Fc` | This *models* "all real executions." It's the standard model, but it's an **assumption**: soundness is "over-approximates `concreteLfp Fc`," which only matters if `Fc` is the real concrete transfer. |
| `Fc` (the parameter to `solve_sound`/`postfixpoint_sound`) | supplied by caller | the concrete transfer being abstracted | **This is the biggest vacuity risk.** `solve_sound` is *parameterized* by `Fc`. Plug in a `Fc` that doesn't model VeIR's semantics and the theorem says nothing useful. The per-op lemmas (doc 04) pin the *arithmetic* to the real interpreter, but the assembled `solve_sound` still takes `Fc` abstractly. |
| `OpTransfer.Sound` (its `eval` parameter) | `SparseAnalysis.lean` | per-op soundness vs. a concrete `eval` | Same caveat: `eval` is a parameter. `sound_top` shows it's dischargeable; the real content is instantiating `eval := OperationPtr.interpret`, done per-op in doc 04 but not threaded into one closed theorem. |
| `Eqn.sound` (the field) | `ConstantSoundness.lean` | each value's abstract transfer over-approximates its concrete one | The end-to-end `ConstantPropagation.solve_sound` is only as strong as the `Eqn`s you build. `constEqn`/`addiEqn` are checked against the interpreter; an `Eqn` with a bogus `con`/`abs` would still typecheck. |
| `hdep`, `hkeys`, `hinv` (hypotheses of `solve_postfixpoint`/`solve`) | `MonotoneFramework.lean` | dependency-completeness of `enqueue`; `keys` enumerates all keys; the worklist covers violated keys | These are *assumptions* the caller must discharge. The fixpoint guarantee is conditional on them; a real instantiation must prove them for the actual `enqueue`/worklist. |
| `FiniteHeight` instances | `ConstantDomain.lean` etc. | the lattice has the claimed finite height | Lower risk — these are *proved* (`rank_lt_of_lt`, `rank_le_maxRank`), so a wrong `rank` can't typecheck. Still worth a glance that `rank` matches the intended height. |

Rule of thumb while auditing: for each soundness theorem, ask **"is the hypothesis
satisfiable, and is the conclusion non-trivial?"** If the answer to either is "not obviously
yes," that's where to look hard.

---

## 8.4 What is explicitly NOT proven

To be unambiguous about scope:

- **The executable `run` is unverified.** `DataFlowFramework.run` is still `partial`; nothing
  proves *it* terminates or that its output matches the proven `solve` model. The proofs are
  about the **abstract model**, not the code you'd actually run. (Docs 03 §3.4, 05, 06.)
- **No end-to-end "SCCP is correct" on the real IR.** The per-op interpreter agreement is
  real, but the full chain "the `HashMap`-backed run over real IR produces a sound result"
  is *not* a single theorem — the SSA-graph reconstruction (gap D) and the `run` bridge
  (gaps B/C) are open.
- **Dominance: nothing.** Deferred entirely.
- **Precision/optimality is not claimed.** Soundness = over-approximation. We prove the
  result is *sound* (never wrong by omission); we do **not** prove it's the *most precise*
  sound result (the `solve_sound`/`postfixpoint_sound` direction is over-approximation, not
  a two-sided characterization). `solve` *does* compute a fixpoint, and `iterateFrom` the
  *least* one, but the assembled end-to-end statement is one-directional soundness.
- **Performance, the interpreter's own correctness, and VeIR's IR well-formedness** are all
  out of scope and assumed.

---

## 8.5 Reproduce and audit it yourself

Everything is checkable in a few commands from the repo root:

```bash
# 1. Build the verified library (the proof IS the successful build).
lake build Veir.Analysis
# ConstantSoundness is a legacy file not imported by Veir.Analysis — build it explicitly:
lake build Veir.Analysis.DataFlow.ConstantSoundness

# 2. Confirm there are no escape hatches.
grep -rnE 'sorry|admit|axiom |native_decide|unsafe ' Veir/Analysis/   # expect: nothing

# 3. Confirm the axiom base of the capstone theorems (in an editor or scratch file):
#    #print axioms Veir.ConstantPropagation.solve_sound   -- [propext, Quot.sound]
```

To audit a *statement*, the fastest route is to `#check` it and read the type, then read the
**definitions** it mentions (§8.3). Don't read the proof — read what it claims.

---

## 8.6 A compact index of the load-bearing pieces

For navigation and as the concrete targets of §8.3's audit. (Names are exact; files are
under `Veir/Analysis/`.)

**Definitions (the specification — audit these):**
- `AbstractDomain` / `γ` / `FiniteHeight` — `DataFlow/Domains/AbstractDomain.lean`
- `AbstractConstant`, `eq_constant_of_le` — `DataFlow/Domains/ConstantDomain.lean`
- `Monotone`, `potential`, `concreteLfp` — `DataFlow/MonotoneFramework.lean`
- `OpTransfer`, `OpTransfer.Sound`, `Extensive` — `DataFlow/SparseAnalysis.lean`, `DataFlow/Soundness.lean`
- `γRuntime`, `Eqn` — `DataFlow/ConstantSoundness.lean`
- `transfer`, `foldBinary?`, `foldedOrTop` — `DataFlow/SparseConstantPropagationAnalysis.lean`

**Theorems (the guarantees — trust these, given the definitions):**
- Termination: `iterateFrom`, `solve` *are total definitions* (acceptance = proof); `potential_update_lt`.
- Fixpoint: `iterateFrom_isFixpoint`, `lfp_isFixpoint`, `lfp_least`, `solve_postfixpoint`.
- Soundness (abstract): `iterateFrom_preserves`, `lfp_preserves`, `postfixpoint_sound`, `solve_sound`.
- Fact store: `getFact?_modifyFact_self`/`_of_ne`, `…ModifyFactAndPropagate…`, `propagate_preserves_lattice`.
- Sparse step: `joinLatticeElement_extensive`, `transfer_monotone`, `foldBinary?_eq`.
- Interpreter agreement: `γRuntime_constant`, `foldBinary?_γRuntime_sound`,
  `addi`/`muli`/`subi`/`andi_γRuntime_sound`, `γRuntime_int_mem`.
- End-to-end: `ConstantPropagation.solve_sound`, `constEqn`, `addiEqn`.

---

## 8.7 Bottom line

The **proofs are maximally trustworthy** — kernel-checked, no `sorry`, no exotic axioms,
`Classical.choice`-free. The honest caveats are entirely about **scope and specification**:
this verifies the *algorithm* (terminates, computes a fixpoint, is sound) and the
*constant-propagation arithmetic against the real interpreter*, at the level of a faithful
**abstract model** — not the executable `run`, and not as a single closed "the optimizer is
correct" theorem. If you build on it, the thing to keep re-checking is §8.3: that the
definitions still say what you mean.
