# 4. Constant propagation and its soundness

Files: `Veir/Analysis/DataFlow/Domains/ConstantDomain.lean`,
`Veir/Analysis/DataFlow/SparseConstantPropagationAnalysis.lean`,
`Veir/Analysis/DataFlow/ConstantSoundness.lean`.

This is where the abstract framework (docs 02–03) meets a real analysis and the *actual
VeIR interpreter*. The chain of results proves: sparse constant propagation's transfer
function agrees, operation by operation, with how the interpreter really evaluates
arithmetic — and assembles into an end-to-end "the constant-propagation fixpoint is sound"
theorem.

---

## 4.1 The constant lattice (`ConstantDomain.lean`)

```lean
inductive AbstractConstant
  | top            -- ⊤: could be anything
  | bottom         -- ⊥: not yet known / unreachable
  | constant (value : ConcreteConstant)
```

This is the classic constant-propagation lattice, height 3: `⊥ < constant c < ⊤`. The
file proves it is a genuine bounded join-semilattice (`le_refl`/`le_trans`/`le_antisymm`,
`le_join_left`/`le_join_right`/`join_le`), an `AbstractDomain` (with concretization
`γ (constant c) = {c}`, `γ ⊤ = everything`, `γ ⊥ = ∅`, and the three soundness laws), and
a `FiniteHeight` instance (`rank` = `0/1/2`, `maxRank = 2`). One small but pivotal lemma:

```lean
theorem eq_constant_of_le (a) (c) : a ≤ .constant c → a ≠ ⊥ → a = .constant c
```

"the only things below a constant are `⊥` and that constant itself." This is the lattice
fact behind constant-folding monotonicity and the operand analysis in §4.4.

---

## 4.2 The transfer and a real finding: SCCP is *not* monotone

`SparseConstantPropagationAnalysis.lean` gives the pure `transfer : OpTransfer AbstractConstant`:
region ops and unrecognized ops yield `⊤`; `arith.constant` yields the constant;
`arith.{addi,muli,subi,andi}` *fold* their operand abstractions via `foldBinary?` (which
only fires when both operands are known constants) wrapped by `foldedOrTop` (constant on
success, `⊤` on failure).

While proving `transfer_monotone` we surfaced a genuine subtlety:

> **`transfer` is not monotone in general.** Counterexample: operands `#[⊥, ⊥]` are `≤`
> `#[constant c, constant d]`, but `addi` cannot fold through `⊥`, so it returns `⊤`,
> whereas it folds the larger operands to `constant (c+d)` — and `⊤ ≰ constant (c+d)`.

Monotonicity only holds on **`⊥`-free** operands. This is not a bug — it's *why* the
driver's "wait until every operand is initialized" guard exists. That guard restricts
`transfer` to the sub-lattice where it *is* monotone, which is what the monotone framework
(doc 02) requires. So the monotone step the framework iterates is the **guarded driver
step**, not the raw `transfer`. `transfer_monotone` is therefore stated with a `⊥`-free
hypothesis, and its docstring records the counterexample.

A second finding, also recorded: `foldedOrTop` returns a length-1 array on success but a
length-`numResults` array on failure, so the clean monotonicity statement implicitly
relies on these being single-result ops — a latent fragility worth a fix or an arity
hypothesis.

`foldBinary?_eq` is the reusable extraction lemma: if `foldBinary?` folds two same-width
constants to a result, that result is exactly what the fold function `f` computed. (Its
proof had to invoke `Data.LLVM.Int.cast_self` — the bitwidth cast in `foldKnownBinary?` is
the identity when both widths are equal.)

---

## 4.3 The interpreter bridge (`ConstantSoundness.lean`)

`solve_sound` (doc 02) needs a concretization to the **values the interpreter actually
manipulates** — `RuntimeValue` — not the abstract `ConcreteConstant`. So we add a second
concretization and `AbstractDomain` instance:

```lean
def γRuntime : AbstractConstant → Set RuntimeValue
  | .top        => fun _  => True
  | .bottom     => fun _  => False
  | .constant c => fun rv => rv = .int c.bitwidth c.value

instance : AbstractDomain AbstractConstant RuntimeValue where
  toJoinSemilattice := inferInstance      -- reuse the same lattice
  γ := γRuntime; γ_top := rfl; γ_bot := rfl; γ_monotone := γRuntime_monotone
```

Same lattice, new `γ` denoting interpreter values. Now `postfixpoint_sound`/`solve_sound`
can be instantiated at `Concrete := RuntimeValue` — the abstract soundness theorems have a
target that is the *real* semantics.

> **A practical wrinkle:** the interpreter (`Veir.Interpreter.Basic`) is a *legacy*
> (non-`module`) file, and Lean's module system forbids a `module` file from importing a
> non-`module` one. So `ConstantSoundness.lean` is deliberately a legacy file (`import`,
> no `module`/`public section`) — the only way to reference both the new `module`-based
> framework and the interpreter. Any future interpreter-touching proof must do likewise.

---

## 4.4 Per-operation soundness vs. the interpreter

The core reusable lemma:

```lean
theorem foldBinary?_γRuntime_sound (bw lv rv) (f) (g) (hfg : ∀ v, f lv rv = some v → v = g) :
    (.int bw g : RuntimeValue) ∈ γRuntime ((foldBinary? #[.constant ⟨bw,lv⟩, .constant ⟨bw,rv⟩] f).getD ⊤)
```

"if the abstract fold `f` agrees with the concrete binary op `g` whenever it succeeds, then
the interpreter's result `.int bw g` lies in the concretization of the transfer's
abstraction" — `⊤` covers the failure case, the matching constant covers success. From it:

| Lemma | Op | Interpreter `g` |
|---|---|---|
| `γRuntime_constant` | `arith.constant` | `BitVec.ofInt` (identical to `Data.LLVM.Int.constant`) |
| `addi_γRuntime_sound` | `arith.addi` | `Data.LLVM.Int.add … nsw nuw` |
| `muli_γRuntime_sound` | `arith.muli` | `Data.LLVM.Int.mul …` |
| `subi_γRuntime_sound` | `arith.subi` | `Data.LLVM.Int.sub …` |
| `andi_γRuntime_sound` | `arith.andi` | `Data.LLVM.Int.and` (poison-propagating bitand) |

Each is proven by casing on the interpreter's result: a `.poison` result makes the fold
fail (→ `⊤`, sound); a `.val` result matches the fold's constant. So **every arithmetic
operation SCCP folds is proven to agree with the interpreter's real semantics.**

---

## 4.5 The end-to-end theorem: the equation model

Finally we package these into a soundness theorem for the whole analysis, via an
*equation system*. Each value carries an equation:

```lean
structure Eqn (K : Type) where
  abs   : (K → AbstractConstant) → AbstractConstant      -- abstract transfer
  con   : (K → Set RuntimeValue) → Set RuntimeValue      -- concrete transfer (interpreter values)
  sound : ∀ σ C, (∀ j, C j ⊆ γRuntime (σ j)) → con C ⊆ γRuntime (abs σ)
```

`ConstantPropagation.solve_sound` then instantiates `MonotoneFramework.solve_sound` with
the equations' transfers; `hfsound` falls straight out of each equation's `sound` field
(the operand-soundness hypotheses are reflexivity when `C = γRuntime ∘ σ`):

```lean
theorem solve_sound … :
    ∀ k, concreteLfp (fun C k => (eqns k).con C) k ⊆ γRuntime (solve … (fun k σ => (eqns k).abs σ) … k)
```

**The constant-propagation worklist fixpoint over an equation system over-approximates the
concrete collecting semantics.** And the equations are populated by the *real* arithmetic:

- `constEqn` — `arith.constant` is a sound equation, via `γRuntime_constant`.
- `addiEqn` — `arith.addi` is a sound equation. Its `sound` proof cases each operand with
  `γRuntime_int_mem` ("an `int` runtime value concretizes only `⊤` or its exact
  constant"): a `⊤` operand makes the fold yield `⊤` (captures everything); matching
  constants invoke `addi_γRuntime_sound`. `muli/subi/andi` follow the same shape.

So the full arc is closed at the equation-model level: **termination** (the abstract
`solve`), **fixpoint** (`solve_postfixpoint`), and **soundness against the interpreter**
(`solve_sound` + the per-op lemmas), assembled into one theorem about constant propagation.

What remains is *only* binding this proven model to the concrete `HashMap`-backed `run`
loop — doc 05.
