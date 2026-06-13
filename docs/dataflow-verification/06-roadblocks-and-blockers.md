# 6. Roadblocks, hangups, and blockers — a field guide

If you sit down to push this verification further (or redo it), this chapter is the
"here be dragons" map. It has two parts:

- **§6.1 Standing blockers** — the big things that are genuinely *not done* and will eat
  weeks, with an honest difficulty read. Read this *before* you commit to "I'll just prove
  `run` terminates."
- **§6.2 The hazard catalogue** — the smaller traps that actually cost time during this
  work. Each is a real incident from the diff, with the symptom and the fix, so you
  recognize them in seconds instead of hours.

---

## 6.1 Standing blockers (the expensive ones)

These are summarized in [05-status-and-further-reading.md](./05-status-and-further-reading.md);
here is the *difficulty-and-why* read.

### Blocker 1 — total-izing the concrete `run` (gaps B + C)

**What it is:** turning `DataFlowFramework.run` from `partial def` into a total,
well-founded definition, so it has a termination *theorem* rather than a termination
*assumption*.

**Why it's hard, concretely:**
- The measure must be a **potential over a two-level heterogeneous `HashMap`**
  (`HashMap LatticeAnchor (DHashMap FactKind Fact)`). `Std.HashMap` has **no
  `sum`-after-`insert` lemma** — you get only `toList_insert_perm`
  (`(m.insert k v).toList ~ ⟨k,v⟩ :: m.toList.filter (k ≠ ·)`), so the decrease proof goes
  through `List.Perm` + filter + sum, at *both* map levels. That's a self-contained but
  large development before you've touched dataflow at all.
- It needs a **per-`FactKind` rank** (`FactSpec.rank`/`maxRank`). For sparse/liveness
  that's easy (their domains have `FiniteHeight`). For **dominator** facts the lattice is
  the dominator-tree refinement — giving it a finite-height rank is its own mini research
  problem.
- `run` is generic over an **arbitrary `visit`** (a black box). It can only terminate if
  every analysis' `visit` satisfies *extensiveness* (only raises facts) and *productivity*
  (enqueues only on change). Proving that for the *real sparse driver* means reasoning
  about `subscribeToOperand`, several `joinLatticeElement`s, a `propagate` loop, and
  executability gating — all mutating the `HashMap`. This is the bulk of the work and it
  is **specific to each analysis**.

**The trap:** "I'll just defer dominance and it'll be tractable." It won't — dominance is
an *additional* deferral, not the blocker. The blocker is the HashMap potential + the
imperative sparse driver, which you need regardless.

**If you must:** the only sane first brick is a *standalone, reusable* `HashMap`
potential-decrease lemma proved via `toList_insert_perm` — no dataflow, no dominator. Get
that green and reusable before anything else.

### Blocker 2 — the interpreter `eval` / SSA-graph reconstruction (gap D)

**What it is:** binding the abstract `Eqn`/`solve_sound` model to the *real* IR — building
each SSA value's equation from its defining op and the actual interpreter.

**Why it's hard:**
- The interpreter is **monadic** (`Interp = Option (UBOr α)`, with undefined-behaviour and
  failure) and stateful (memory). Extracting "the result value of this op" means threading
  that monad.
- It reads op data (`getOpType!`, `getProperties!`, `getResultTypes!`) from the
  `IRContext`; relating those to what the abstract `transfer` reads is IR-consistency
  plumbing.
- It lives in a **legacy (non-`module`) file**, so everything touching it must too (see
  §6.2, hazard "module imports").

**Status:** the *per-operation* arithmetic soundness is done (doc 04) — that's the
mathematically interesting part. What remains is the graph reconstruction, which is
plumbing, not insight.

### Blocker 3 — dominance

Deferred entirely. Dominance doesn't use a clean finite-height *abstract domain* the way
sparse/constant/liveness do; its lattice and transfer are the Cooper–Harvey–Kennedy
dominator algorithm. Proving its `visit` monotone (gap C for dominance) and giving it a
`rank` (gap B) is a separate effort. Leave it `sorry`/`partial` until the very end.

---

## 6.2 The hazard catalogue (the time-sinks)

Every one of these actually happened. The pattern is the same: a construct that *runs*
fine but *resists proof*. Learn the symptom→fix pairs.

### H1. `cast` / `Eq.rec` over data
- **Symptom:** a definition transports data across a *type equality* (`cast h x`). Every
  downstream proof drowns in `cast_cast`, `eqRec_eq`, `HEq` obligations.
- **Fix:** don't. Replace the equality with an **explicit isomorphism + round-trip laws**
  (`toX`/`ofX` with `of_to`/`to_of`). In the common case the maps are `id` and the laws are
  `rfl`, so runtime is unchanged, but now you have `@[simp]` round-trip lemmas that fire
  automatically. (This branch: `SparseFactSpec`, doc 03 §3.2.)

### H2. `partial def` is invisible to the logic
- **Symptom:** you want to prove something about a `partial def`. You can't induct on it,
  `rw [f]` doesn't unfold it usefully, there's no `.induct`.
- **Fix:** either re-express it as **well-founded recursion** (`termination_by` +
  `decreasing_by`) and prove properties via the generated `f.induct`, or prove a *separate
  total model* and relate it. (This branch: `solve` is the total model of `run`.)

### H3. Section variables not auto-included in `termination_by`/`decreasing_by`
- **Symptom:** `failed to synthesize FiniteHeight α` *inside* `termination_by`, even though
  `variable [FiniteHeight α]` is right there. Cause: Lean includes a section variable only
  if the *body* mentions it; the body uses `FiniteHeight` only in the *measure*, so it's
  dropped from the signature.
- **Fix:** put the needed instances as **explicit binders on the definition itself**
  (`def f [FiniteHeight α] …`), not as section variables. `include` did *not* reliably fix
  this for the termination context. (This branch: `iterateFrom`, `solve`.)

### H4. Cross-module unfolding needs `@[expose]`
- **Symptom:** `simp only [foo]` / `rw [foo]` does nothing, or "definition is not exposed,"
  for a `def` from another `module` file.
- **Fix:** mark the def `@[expose]` where it's defined. (This branch: `Fact.propagate`,
  `joinLatticeElement` had to be exposed to unfold in proofs.)

### H5. `module` files can't import non-`module` files
- **Symptom:** `cannot import non-module X from module`.
- **Fix:** make *your* file a **legacy file** (`import`, no `module`/`public section`).
  Legacy files can import both kinds; `module` files can only import `module` files. (This
  branch: `ConstantSoundness.lean` imports the legacy interpreter, so it's legacy too.)

### H6. Instance diamonds (two paths to the same class)
- **Symptom:** a lemma's `⊔` (from `JoinSemilattice.toJoin`) "doesn't match" the goal's `⊔`
  (from a standalone `[Join Domain]`). `exact le_join_left` fails with two identical-looking
  but instance-distinct terms.
- **Fix:** don't carry redundant instances. If `JoinSemilattice` already provides `Join`,
  *don't* also take `[Join Domain]`. (This branch: dropping the standalone `[Join Domain]`
  and `[Std.IsPartialOrder Domain]` from `joinLatticeElement_extensive`.)

### H7. A *free* instance argument picks the wrong instance
- **Symptom:** you want `Fact.propagate` to be `SparseFact.propagate`, but the theorem took
  `[FactSpec kind]` as a hypothesis, so it's an *arbitrary* `FactSpec` and the defeq fails.
- **Fix:** *remove* the free instance binder and let synthesis pick the canonical one (here,
  the sparse `FactSpec` derived from `[Bot Domain]`). Fewer explicit instances can be
  *more* correct. (This branch: `joinLatticeElement_extensive`.)

### H8. `Set` membership won't reduce under `simp`
- **Symptom:** goal `x ∈ (fun _ => True)` left unsolved by `simp` (the `Set`/`Membership`
  application doesn't unfold).
- **Fix:** it's *definitionally* `True`/the predicate — close with `exact trivial`, or use
  `show <the predicate>` to convert membership to the underlying `Prop` and proceed. (This
  branch: the `⊤` cases of `γRuntime_monotone`, `foldBinary?_γRuntime_sound`, `addiEqn`.)

### H9. `cases h : e` rewrites the *goal*, not just the hypothesis
- **Symptom:** after `cases hf : f x`, your goal mysteriously has `f x` replaced by the
  pattern, and a term you built for the original goal no longer typechecks.
- **Fix:** know that `cases h : e` generalizes `e` everywhere. If you only want to name the
  case, prefer `by_cases`/`rcases`, or structure so the substitution is what you want.
  (This branch: the first `foldBinary?_eq` and `solve_postfixpoint` attempts.)

### H10. Recursive *theorems* with `termination_by` can silently not run your tactics
- **Symptom:** every base-case subgoal shows as "unsolved" *identically* no matter what
  tactic you write — the equation compiler isn't elaborating your branch the way you think.
- **Fix:** prove properties of a WF def with its generated **`f.induct`** principle
  (`induction x using f.induct with | case1 … | case2 …`) instead of re-rolling the
  recursion in a `theorem` body. (This branch: `solve_postfixpoint` only worked via
  `solve.induct`.)

### H11. WF defs don't reduce by `rfl`/`rw`; use the equation lemmas
- **Symptom:** `solve … store []` won't reduce to `store` by `rfl`, and `rw [solve]` leaves
  an un-reduced `match`.
- **Fix:** `simp only [solve]` uses the **per-pattern equation lemmas** (`solve.eq_1`, …)
  and reduces the base case; for the recursive case `rw [solve]` (one unfold) then `split`.

### H12. Dependent types and `HEq`
- **Symptom:** `.int bw lv = .int bw' x` gives you a `HEq lv x` (the values live in
  `Int bw` vs `Int bw'`), not a plain equality.
- **Fix:** `injection h with hbw hlv` → `subst hbw` (unify the indices) → `eq_of_heq hlv`
  (now homogeneous). (This branch: `γRuntime_int_mem`.)

### H13. `Id.run do` wrappers block reduction
- **Symptom:** a goal like `v = Id.run v` after unfolding a `do`-based definition.
- **Fix:** add `Id.run` to the `simp` set. (This branch: `andi_γRuntime_sound`, because
  `Data.LLVM.Int.and` is `Id.run do …`.)

### H14. Array-literal / `getElem?` reduction needs *full* `simp`
- **Symptom:** `simp only […]` won't compute `#[a,b].size`, `#[a,b][0]?`, or resolve
  `if 0+1+1 ≠ 2`.
- **Fix:** use full `simp` (it carries the array-literal and arithmetic simprocs), or chase
  the specific lemmas (`List.getElem?_cons_zero`, `Nat.reduceAdd`, …). (This branch:
  `foldBinary?_eq`.)

### H15. Lemma names you'll guess wrong (no Mathlib here)
VeIR doesn't depend on Mathlib, so Mathlib names are absent and the Std names differ.
Real misses from this session and their resolutions:
- `eq_or_ne` → **doesn't exist**; use `by_cases h : a = b`.
- `Option.map_eq_some'` → it's `Option.map_eq_some_iff`.
- `Array.size_toArray` → it's `List.size_toArray`.
- HashMap lawfulness comes from `instLawfulHashableOfLawfulBEq` (derived from `LawfulBEq`).
- The cast-over-equal-widths identity was already in-tree: `Data.LLVM.Int.cast_self`.
- The HashMap insert/perm lemmas: `Std.HashMap.get?_insert_self`, `getElem?_insert`,
  `toList_insert_perm`.
> **The fix for *all* of these:** don't guess — *search*. See doc 07 §7.4 (`exact?`,
> `apply?`, Loogle, grepping the toolchain source).

### H16. The linters that will nag you
- `unusedSectionVars`, `unusedSimpArgs`, `unusedVariables`. Mostly they're *helpful*
  (e.g. `unusedSimpArgs` tells you which lemmas actually fired — a debugging tool, doc 07).
  But a genuinely-used-only-in-`decreasing_by` binder (the `dite` witness `h` in
  `iterateFrom`/`solve`) trips `unusedVariables`; silence it locally with
  `set_option linter.unusedVariables false in` immediately before the def.

---

## 6.3 The meta-lesson

Skim §6.2 and you'll notice **almost none of the time went into the mathematics.** It went
into making constructs *legible to the kernel*: `cast`→iso, `partial`→WF, free
instances→canonical instances, membership/`Id.run`/array-literal reductions, and finding
the right Std lemma name. Budget accordingly: for a proof like this, expect the ratio of
"fighting the encoding" to "doing the math" to be something like 4:1. The next chapter is
the toolkit for winning those fights faster.
