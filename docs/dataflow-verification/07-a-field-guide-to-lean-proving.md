# 7. A field guide to Lean proving

This chapter is the toolkit — the tactics, strategies, idioms, and workflow that actually
moved this proof forward, plus a learning path aimed at someone who wants to do *complex*
Lean proofs (not "prove `2 + 2 = 4`"). It assumes you've seen basic Lean; it tries to teach
the things the introductory material under-emphasizes. Resources are at the end, chosen to
be **less obvious** than the standard *Theorem Proving in Lean 4*.

---

## 7.1 The one mental model that matters

> **A proof is a fight between you and the kernel's *definitional equality* (`defeq`).**

Most of your time isn't "is this true?" — it's "can the kernel *see* that this is true
without unfolding something it refuses to unfold?" Almost every hazard in doc 06 is a
`defeq` problem in disguise: `cast` blocks unfolding; `partial` is opaque; `@[expose]`
controls cross-module unfolding; `Set` membership is *defeq* to a predicate but `simp`
won't *rewrite* it; `Id.run x` is *defeq* to `x` but stays in the term.

Two corollaries shape everything below:

1. **Design for defeq.** When *you* control a definition, choose the encoding that makes
   the facts you'll need hold *by `rfl`* or by a `@[simp]` lemma. (The `cast`→iso rewrite,
   `concreteLfp` as an intersection so leastness is definitional, pure `OpTransfer` instead
   of `DataFlowContext` mutation.)
2. **When you don't control it, learn its reduction rules.** WF defs reduce via their
   `.eq_n` equation lemmas (`simp only [f]`), not `rfl`. Cross-module defs need `@[expose]`.
   `Id.run`/membership need to be in the `simp` set.

---

## 7.2 The core tactic vocabulary (as actually used)

You can go very far with a small set. In rough order of how often they appeared here:

- **`simp` / `simp only [lemmas] at h ⊢`** — the workhorse rewriter. `simp only` is
  *controlled* (only the lemmas you name + structural reductions); plain `simp` adds the
  global `@[simp]` set and the simprocs (array literals, `Nat` arithmetic). Rule of thumb:
  reach for `simp only` first (predictable); escalate to full `simp` when you need
  array/`Nat`/`Id.run` reduction (hazards H8, H13, H14).
- **`rw [h]` / `rw [← h]`** — rewrite by an equation, left-to-right (or reverse). Closes
  `a = a` goals automatically but **not** `a ≤ a`. Fails loudly if the pattern isn't found
  (a feature — it tells you your term doesn't look how you think).
- **`exact` / `refine ?_`** — supply the proof term; `refine` leaves holes. `exact`
  succeeds up to `defeq`, which is why `exact trivial` closes `x ∈ (fun _ => True)`.
- **`intro`, `rintro ⟨…⟩`** — introduce hypotheses; `rintro` destructures (`∃`, `∧`, `=` via
  `rfl`) in one shot.
- **`cases` / `rcases` / `by_cases` / `obtain`** — case analysis. `by_cases h : P` for a
  decidable split; `rcases`/`obtain` to destructure; `cases h : e` *also generalizes the
  goal* (hazard H9 — know this).
- **`split`** — case-split on an `if`/`match` *inside the goal*. Indispensable for
  functions defined by `if`/`match` (the whole sparse `transfer`).
- **`omega`** — decides linear `Nat`/`Int` (in)equalities. The potential-decrease proofs
  end in `omega`. Use it for *any* arithmetic side goal.
- **`induction x using f.induct`** — the secret weapon for WF definitions (§7.3).
- **`subst`, `injection`, `eq_of_heq`** — equality plumbing, especially for dependent types
  (hazard H12).
- **`calc`** — readable equational/inequational chains (note: needs the right `Trans`
  instances; we hit a case where `≤` then `=` didn't chain and switched to `rw`).

Automation worth adopting (easy to forget they exist):
- **`grind`** — Lean's newer SMT-inspired workhorse: congruence closure + linear arithmetic
  + a commutative-ring solver + case-splitting, all sharing a "whiteboard" of derived facts.
  The first thing to try on a goal that's "obviously true but tedious." (`@[grind]`-annotated
  library lemmas are found automatically.)
- **`aesop`** ("Automated Extensible Search for Obvious Proofs") — white-box best-first proof
  search; integrates `simp`, extensible via `@[aesop]` rules, and `aesop?` prints the script
  it found. It's the engine behind Mathlib tactics like `measurability`/`continuity`.
- **`decide`** — closes *decidable* propositions by computation (small finite facts);
  **`bv_decide`** discharges bit-vector/Boolean goals via an external SAT solver with a
  checkable certificate (handy for low-level/compiler work).
- **Hammers** (emerging): `LeanHammer` / `lean-auto` + `Duper` route goals to external ATPs
  (Vampire, E, Z3, …) and reconstruct the proof. Not yet a daily driver, but worth watching.

> Keep the community **Lean tactic cheatsheet** (`leanprover-community.github.io/papers/lean-tactics.pdf`)
> on hand — a printable one-pager of the full tactic set, updated regularly.

---

## 7.3 Strategies that were decisive here

### Well-founded recursion + functional induction
When a recursive definition isn't structurally decreasing, give it
`termination_by <measure>` and discharge `decreasing_by` with the proof the measure drops.
**The definition compiling is the termination theorem** — there's nothing else to prove.
Then, to prove *properties* of that function, use the auto-generated **`f.induct`**
principle:
```lean
induction x, hx using f.induct with
| case1 … => …
| case2 … ih => …   -- `ih` is the inductive hypothesis for the recursive call
```
This was the only thing that worked for `solve_postfixpoint` — re-deriving the recursion in
a `theorem` body silently failed (hazard H10). `f.induct` *gives you the IH for free* with
the right hypotheses in scope.

### Lexicographic measures
For "either this shrinks or, if not, that shrinks" termination (the worklist),
`termination_by (a, b)` uses the lexicographic order on the pair, and `decreasing_by` gets
a `Prod.Lex` goal — close the first component with `Prod.Lex.left` (strict drop in `a`) or
the second with `Prod.Lex.right` (equal `a`, strict drop in `b`).

### Make leastness/soundness *definitional*
We needed "the collecting semantics is below any post-fixpoint." Instead of building
Knaster–Tarski machinery, we *defined* the collecting semantics as the intersection of all
post-fixpoints (`concreteLfp`). Then leastness is `fun y hy => …` — true by unfolding. **If
a theorem is hard, try changing the definition so the theorem becomes easy.** This is the
single highest-leverage move in the whole branch.

### Parameterize by the hard hypothesis
`getFact?_modifyFactAndPropagate_self` takes a hypothesis "`propagate` preserves the store"
rather than knowing it internally. This lets the *generic* framework lemma stay generic,
while the *specific* instance (`SparseFact.propagate_preserves_lattice`) discharges it.
Push analysis-specific facts to the leaves.

### `getElem?` (Option) to dodge bound proofs
Indexing `xs[i]` needs a proof `i < xs.size`. Stating things with `xs[i]? = some a`
(returning `Option`) sidesteps the bound entirely and is usually what you want for
soundness specs (`OpTransfer.Sound`, `ArrayLe`).

### Minimal typeclasses per declaration
Carrying redundant instances causes diamonds (hazard H6) and inclusion problems (H3). Give
each definition exactly the instances it uses; if `JoinSemilattice` already implies `LE`
and `Join`, don't also take them.

### `show` to exploit `defeq`
When the goal is *defeq* to something more convenient (membership ↦ predicate, `getD some`
↦ the value), `show <the convenient form>` re-states it for free, then proceed. Pairs with
`exact trivial` for membership-in-`⊤`.

---

## 7.4 Search-driven proving — the biggest practical lever

You will not memorize library lemma names, and **guessing wastes more time than anything
else** (hazard H15). Make searching reflexive:

- **`exact?`** — "find me a lemma/hypothesis that closes this goal." Try it on every leaf
  goal before writing anything.
- **`apply?`** — like `exact?` but for partial application.
- **`rw?`** — "what can I rewrite here?"
- **`simp?` (a.k.a. `simp only [...]` "squeeze")** — runs `simp` and *prints the exact
  lemma set it used*, so you can pin it down to `simp only`. Also: the **`unusedSimpArgs`
  linter is a debugger** — it tells you which of your named lemmas actually fired, which
  reveals what `simp` is really doing.
- **Loogle** (`loogle.lean-lang.org`, by J. Breitner) — search *by shape*: type patterns
  like `?a ⊔ ?b = ?b ⊔ ?a` or `List.Perm`, name fragments, or "lemmas mentioning both
  `insert` and `get?`." Use it when you know the *form* of what you want. This is how you
  find `toList_insert_perm`, `get?_insert_self`, etc.
- **LeanSearch** (`leansearch.net`) — search by **natural language** ("a constant times a
  sum"); LLM-backed, complements Loogle for when you *don't* yet know the Lean form. (Newer
  semantic engines exist too — LeanExplore, Lean Finder; Moogle is older and less current.)
  The community guide *"Searching for Theorems in Mathlib"*
  (`leanprover-community.github.io/blog`) compares them and is worth one read.
- **Grep the toolchain source.** The Std/Lean source ships with your toolchain
  (`~/.elan/toolchains/<ver>/src/lean/Std/...`). `grep -rn "theorem get?_insert" …` finds
  the *exact* name and signature. This branch leaned on this constantly (it's how
  `toList_insert_perm` and the cast lemma were found).
- **`#check @Foo.bar`, `#synth C α`, scratch files.** To learn a lemma's exact signature or
  whether an instance exists, write a one-line scratch file and run `lake env lean
  scratch.lean`, or use `#check`/`#synth` in-buffer. `#synth LawfulBEq LatticeAnchor` is how
  we discovered the lawful-instance gap (A) before writing any proof.

> Workflow tip used throughout: **run builds in the background and read the *error's goal
> state*.** The single most informative thing in Lean is the `⊢ …` the compiler prints when
> a tactic fails — it tells you the *exact* term shape, which then tells you the lemma to
> search for. Treat a failed build as a free oracle, not a setback.

---

## 7.5 Debugging a stuck proof

A checklist, in order:

1. **Read the actual goal** (`⊢`) and *every* hypothesis the error prints. Half the time the
   fix is visible there.
2. **`set_option trace.Meta.synthInstance true`** when an instance won't synthesize — it
   shows the search and where it dead-ends.
3. **`set_option pp.all true`** (or `pp.explicit`, `pp.notation false`) when two terms
   "look identical but don't unify" — it reveals the hidden instance/implicit mismatch
   (this is how you *see* an instance diamond, hazard H6).
4. **Bisect a failing `simp`/`rw`** by switching to `simp only` with one lemma at a time, or
   inserting `sorry` after a step to inspect the intermediate goal.
5. **Check it's a `defeq` problem.** Try `rfl`, `exact trivial`, `show <other form>`. If the
   thing is defeq, you just need to *say* so.
6. **Suspect the encoding.** If a proof is fighting you for more than a few minutes, ask
   whether a *definition* should change (H1, H2, the "make it definitional" move) rather
   than the proof.

---

## 7.6 A learning path (with deliberately non-obvious resources)

The standard *Theorem Proving in Lean 4* teaches the syntax; it under-teaches the *craft*
(search, defeq intuition, WF recursion, debugging). These fill those gaps:

**Start here (craft-first, problem-driven):**
- **Heather Macbeth, *The Mechanics of Proof*** (`hrmacbeth.github.io/math2001`). A genuinely
  different pedagogy — teaches *proving* (not just Lean) through carefully staged problems.
  The best on-ramp for building real intuition.
- **Blanchette, Avigad et al., *The Hitchhiker's Guide to Logical Verification*** (free PDF;
  the basis of courses at VU Amsterdam / CMU). Heavier on the *verification* mindset and
  tactics than TPIL; excellent on induction, simp, and proof structure.

**For the things this branch actually needed:**
- **David Christiansen, *Functional Programming in Lean*** (`lean-lang.org/functional_programming_in_lean`).
  The right book for **monads, `do`-notation, `Id.run`, and dependent types** — exactly the
  machinery behind hazards H12 and H13 and the interpreter's `Interp`. Most "prove math"
  resources skip this, and it's precisely what you need to reason about real code.
- **Joachim Breitner on well-founded recursion & functional induction** — he implemented
  much of Lean's recursion machinery. Start with the official Lean blog posts he authored:
  **"Functional induction"** (`lean-lang.org/blog/2024-5-17-functional-induction/`) and
  **"Recursive definitions in Lean"** (`lean-lang.org/blog/2024-1-11-recursive-definitions-in-lean/`),
  then his own blog (`joachim-breitner.de/blog`) for deeper cuts. These explain *why*
  `termination_by`/`decreasing_by`/`.induct` behave as they do — the single most relevant
  background for doc 02 and hazards H3/H10/H11.
- **The Lean 4 manual's "Well-founded recursion" and "Definitions" sections**
  (`lean-lang.org/doc`) — the authoritative word on equation lemmas, `@[expose]`, reducibility.

**For the metaprogramming-shaped questions ("why does simp/cast behave like this?"):**
- ***Metaprogramming in Lean 4*** (the "Lean 4 Metaprogramming Book",
  `leanprover-community.github.io/lean4-metaprogramming-book`). You don't need to write
  tactics, but understanding elaboration/`defeq`/`whnf` demystifies most of doc 06.

**Search and reference (bookmark these):**
- **Loogle** (`loogle.lean-lang.org`, by J. Breitner) — shape/pattern search. Learn its query
  syntax; it's the fastest way to find a lemma when you *do* know its rough type.
- **LeanSearch** (`leansearch.net`) — natural-language / semantic search, for when you *don't*
  yet know the Lean form ("a constant times a sum"). Newer semantic engines (LeanExplore,
  Lean Finder) exist too; **Moogle** is the older one and now less current.
- **"Searching for theorems in Mathlib"** — the community blog post
  (`leanprover-community.github.io/blog`) that surveys all of the above and when to reach for each.
- **The Lean tactic cheatsheet** (`leanprover-community.github.io/papers/lean-tactics.pdf`) —
  the full tactic set on one printable page.
- **The Std4 / Batteries source** — read it as a curated library of *example proofs*; when
  stuck, find a similar lemma and copy its proof structure.
- **lean-lang.org/doc** and the community **tactic index** — for the full tactic list.

**The actual lifeline:**
- **The Lean Zulip** (`leanprover.zulipchat.com`), especially `#new members` and the maths/
  general streams. Searchable archive of nearly every gotcha in doc 06. When truly stuck,
  a minimal reproduction posted there gets expert answers fast. This is, in practice, where
  most real Lean learning happens.

**Problem-driven practice:**
- **Kevin Buzzard, *Formalising Mathematics*** (course materials online) — weekly problem
  sheets that build serious skill.
- **Glimpse of Lean / Verbose Lean** (Patrick Massot) and the **Natural Number Game** /
  other "games" — for fluency, if you want a gentler ramp than Macbeth.

**The honest meta-advice:** do not read these front to back. Do a *real* small proof, get
stuck, and use the resource (or Zulip, or `exact?`) to get unstuck — then move on. Skill
here is almost entirely a function of *number of stuck-then-unstuck cycles*, and this branch
is itself a worked example of dozens of them.

---

## 7.7 Training to mastery — a multi-year plan (for a verification PhD)

If you're going to live in Lean for the next 4–5 years doing **compiler verification**,
treat skill acquisition as a project with its own plan, not a byproduct of your research.
The good news: this domain has the cleanest possible feedback loop — the compiler tells you
*instantly and objectively* whether you're right — which is the precondition for **deliberate
practice** (the only reliable route to expertise: right-difficulty tasks + immediate
feedback + reflection, repeated). The plan below is how to harness that.

### The core principle: train at the edge of your ability

Every session, work on something where you'll get **stuck a few times but can get unstuck**.
- **Too easy** (no stuck-cycles) → you're rehearsing, not learning. Raise difficulty.
- **Too hard** (stuck > ~1 hour with zero progress) → you're missing a prerequisite. Stop,
  identify the gap (a tactic, a library area, a concept), learn *that*, return.
- After each stuck→unstuck, spend 60 seconds on **reflection**: *what was the actual blocker,
  and what's the reusable lesson?* (Most of doc 06 is exactly these reflections written down
  — keep your own running version; it compounds.)

### A cadence

- **Daily (20–40 min, non-negotiable).** One small, complete proof or one of these:
  - Re-prove a lemma you did last week *without looking* (spaced repetition for proofs —
    you'll be shocked how much rebuilds intuition).
  - Read **one** proof from Batteries/Mathlib/the Lean compiler source and understand *every
    line* — predict each goal state before checking. Reading expert proofs is the most
    underrated training input.
  - Solve one exercise from a problem set (sources below).
- **Weekly.** A bigger bite: a full problem-sheet section, or **formalize one small thing
  from whatever you read this week** (a definition + its basic lemmas). Once you can,
  **open a Batteries/Mathlib PR** for a missing lemma — *code review by maintainers is the
  fastest expertise accelerant that exists*, because it corrects style and idiom you can't
  self-diagnose.
- **Monthly/quarterly.** Formalize a *self-contained chunk*: a small language and a piece of
  its metatheory, or one optimization and its correctness proof. These are dress rehearsals
  for your thesis and surface the project-scale problems (proof performance, structure,
  automation) early.
- **Continuously.** Keep a green build, commit small, and **write** — explain a technique to
  someone (or to future-you). Teaching forces the gaps to the surface; these docs were
  written partly for that reason.

### Where to find right-difficulty challenges (and how to calibrate)

A rough difficulty ladder; climb until a rung makes you struggle productively, then live
there for a while:

1. **Natural Number Game** → fluency with `rw`/`induction`/basic tactics. (Days.)
2. **Heather Macbeth, *Mechanics of Proof*** exercises → real proving habits. (Weeks.)
3. **Kevin Buzzard, *Formalising Mathematics*** weekly sheets → serious tactic skill on
   non-trivial goals. (Months; do them even though they're "maths" — the *skills* transfer
   wholesale to PL/compilers.)
4. **Advent of Code / Project Euler in Lean** → *functional-programming* fluency (data
   structures, `do`-notation, `Id.run`, totality, performance) — the half of Lean that the
   maths-oriented material skips and that **compiler work leans on heavily** (your
   interpreters, IR manipulations, and `decide`-based checks all live here).
5. **Re-formalize lemmas from your own reading / your own research need** → the best
   exercises, because they're *real*. When a paper states a lemma, try to state and prove it
   in Lean before reading their proof.

To *find* exercises beyond these: search the Zulip for "exercises"/"problem set"; browse
`good first issue`/`help wanted` on the **Batteries** and **Mathlib** GitHub; and mine the
*exercise* versions of the canonical PL texts below (they ship with hundreds of graded
problems). Calibration heuristic: skim a problem and predict the *proof shape* (induction on
what? which lemmas?). If you can predict it fully, it's too easy; if you can't even start,
back up a rung.

### Practice arenas — your "LeetCode for Lean"

There *is* a problem-bank ecosystem; treat these like a competitive-programming ladder.

**Gamified, one-theorem-per-level (the most LeetCode-like; start here):**
- **Lean Game Server** — `adam.math.hhu.de`. Browser-based, instant feedback, curated
  tactic set per level. Hosts the **Natural Number Game (NNG4)**, plus **Set Theory**,
  **Logic**, and **Robo** games. The single best "just give me a problem to solve" arena.

**Large problem banks (grind to taste, pick difficulty):**
- **Compfiles** (`github.com/dwrensha/compfiles`, dashboard at `dwrensha.github.io/compfiles`)
  — a catalog of **olympiad/IMO problems formalized in Lean 4**, with a live solved/unsolved
  status board. Pick an unsolved (or solved-then-hide-the-answer) problem and go. The
  closest thing to a LeetCode *problem set* with a difficulty/status dashboard.
- **Lean Workbook** (arXiv 2406.03847) — a **large-scale** bank (tens of thousands) of
  problems formalized from natural-language math. Bank-scale grinding.
- **miniF2F** and **PutnamBench** (`trishullab.github.io/PutnamBench`) — competition
  benchmarks (olympiad / Putnam). Hard; usable as a human problem bank, not just an ML one.

**Books = structured problem sets (graded, fill-in-the-`sorry`):**
- *Mechanics of Proof*, *Mathematics in Lean*, *TPiL* (solutions repo: `github.com/mccorvie/tpil4`),
  *Hitchhiker's Guide* (ships a VSCode exercise project). These are your "easy/medium" ladder
  with worked solutions to check against.

**Courses with problem sets (CS-flavored — relevant to *you*):**
- **UC Berkeley CS 294-268, "Proving TCS and Math Theorems in Lean"**
  (`ucb-lean-course-sp26.github.io`) — *theoretical-CS*-oriented problem sets, closer to
  compiler/PL work than the maths courses.
- **Kevin Buzzard, *Formalising Mathematics*** — weekly sheets (maths, but pure skill).

**Daily-grind for the *functional-programming* half:**
- **Advent of Code in Lean** / **Project Euler in Lean** — for data structures, `do`-notation,
  totality, performance: the skills your interpreters and IR passes need.

> How to use these like LeetCode: pick the arena matching your level (Game Server →
> Compfiles → PutnamBench), timebox each problem, and when stuck, *first* try `exact?`/
> `apply?`/Loogle (your "hints"), *then* peek at a solution (Compfiles/TPiL-solutions), then
> **re-prove it from scratch the next day**. The re-prove step is where the learning sticks.

### The compiler-verification curriculum (the domain, not just the tool)

Lean fluency is necessary but not sufficient — you also need the **techniques of mechanized
semantics**. These are largely Coq/Isabelle/Agda, but the *concepts and proof techniques*
are language-agnostic and are exactly what you'll re-implement in Lean. Prioritize:

- **Nipkow & Klein, *Concrete Semantics*** (free, Isabelle) — *the* on-ramp to mechanized
  programming-language semantics: operational semantics (big/small-step), Hoare logic, and a
  **verified compiler** to a stack machine, all worked end to end. Do its exercises *in
  Lean* as you read. If you read one book on this list, this is it.
- **Software Foundations Vol 2, *Programming Language Foundations*** (Pierce et al., free,
  Coq) — type systems, **progress + preservation** (syntactic type soundness), small-step
  semantics, and a chapter on compiler correctness. The canonical PL-verification course;
  the *Logical Foundations* (Vol 1) chapters on induction/`simp`-style automation are also
  worth porting.
- **Xavier Leroy, *CompCert* papers and his Collège de France lectures on "mechanized
  semantics"** (lecture notes + videos online) — the gold standard for *real* compiler
  verification: **simulation/refinement diagrams**, semantic preservation across passes, the
  whole architecture of a verified compiler. This is the closest thing to a blueprint for a
  compiler-verification thesis.
- **Adam Chlipala, *Certified Programming with Dependent Types* (CPDT)** (free, Coq) — for
  **proof engineering and automation at scale**: how to build proofs that don't collapse
  under their own weight, and how to write tactics/automation so you're not doing everything
  by hand. Essential before your project gets big.
- (Optional, concept-deepening) **PLFA, *Programming Language Foundations in Agda*** — the
  same metatheory with a heavily dependently-typed flavor close to Lean's.

The single **best first project**: formalize a compiler from arithmetic (then boolean, then
`let`, then control flow) expressions to a stack machine, give source and target operational
semantics, and prove the compiler **semantics-preserving**. It's small, it's the "hello
world" of compiler verification, and it exercises every core technique (semantics,
simulation, induction on derivations, well-founded recursion). Do it in Lean in your first
months; you'll redo richer versions for years.

### Specializing in static analysis & abstract interpretation (this branch's home turf)

The curriculum above is *compiler* verification in general (semantics preservation, type
soundness). This branch sits in a specific sub-area — **static analysis / abstract
interpretation / dataflow** — and if that's your thesis direction it deserves its own track.
Chapter 01 has the *background* reading; here is the *training* path to becoming a
practitioner who can design and verify analyses.

**The texts (in increasing depth):**
- **Anders Møller & Michael Schwartzbach, *Static Program Analysis*** (free lecture notes,
  regularly updated) — the best *free* on-ramp. Lattices, monotone frameworks, the worklist
  algorithm, then a clean bridge to abstract interpretation and widening. Read this first;
  it's exactly the material docs 01–02 formalize, presented pedagogically.
- **Xavier Rival & Kwangkeun Yi, *Introduction to Static Analysis: An Abstract Interpretation
  Perspective*** (MIT Press, 2020) — the accessible modern textbook for abstract
  interpretation proper. Galois connections, domain design, widening/narrowing, with real
  domains worked out.
- **Patrick Cousot, *Principles of Abstract Interpretation*** (MIT Press, 2021) — the
  comprehensive, definitive treatment by the founder of the field. Dense; use it as the
  reference you grow into, not the first read.
- **Nielson, Nielson & Hankin, *Principles of Program Analysis*** — the bridge between
  classical dataflow and abstract interpretation (already in doc 01).

**The mechanized-AI track — read the *verified* version of what this branch built:**
- **CompCert's `backend/Kildall.v`** (`github.com/AbsInt/CompCert`) — a **fully verified
  generic dataflow (Kildall worklist) solver** in Coq, reused across CompCert's
  constant-propagation, liveness, value, and dead-code passes. The closest existing relative
  of `MonotoneFramework.solve` + the `run`-bridge: a "total, sound worklist over a
  semilattice," exactly what closes gaps (B)/(C). Its central *fixpoint invariant theorem* —
  "any property preserved by `lub` and `transf` and holding at `bot` holds of the result" —
  is **literally `lfp_preserves`/`postfixpoint_sound` from doc 02**. Two ideas worth stealing
  if you formalize `run`: it abstracts the worklist behind a `NODE_SET` module, and keeps its
  `visited` set as a `Prop`-sorted *ghost* (erased at extraction).
- **Verasco** (Jourdan, Laporte, Blazy, Leroy, Pichardie, POPL 2015) and **David Pichardie's
  line of work on verified abstract interpretation** (his PhD thesis and follow-ons) — the
  canonical references for *formalizing abstract interpretation itself* (concretization,
  soundness via post-fixpoints, fixpoint iteration with widening, abstract domains as a
  verified interface). The architecture mirrors docs 02 + 08 here; reading them shows the
  finished shape.

**The honest gap this branch has — go learn it:** we made fixpoint iteration *terminate*
via **finite height** (the Ascending Chain Condition). **Real abstract domains are not
finite-height** — intervals, congruences, octagons, polyhedra all have infinite ascending
chains, so Kleene iteration *does not terminate* on them. The fix is **widening (`∇`)**: an
over-approximation of join engineered to force convergence after finitely many steps,
followed by **narrowing** to recover precision. Widening/narrowing is *the* defining
technique of practical abstract interpretation and is **completely absent here** precisely
because constant/liveness lattices are finite-height. If you move to non-trivial domains,
this is the first thing to learn (and to verify — Verasco/Pichardie show how). Treat doc 02
as "the finite-height special case where widening isn't needed yet."

**The static-analysis first project (after the stack-machine compiler):** implement and
verify a small **interval analysis** for a toy imperative language — including a **widening
operator** and a proof that iteration-with-widening terminates *and* stays sound. It forces
you to confront everything finite height let this branch avoid.

### Techniques to deliberately drill (compiler-flavored)

Make a point of *practicing each in isolation* until comfortable:
- **Operational semantics** as inductive relations, and **induction on derivations** (not
  just on syntax).
- **Simulation / refinement proofs** (CompCert-style "forward simulation" diagrams) — the
  workhorse of pass correctness.
- **Logical relations** — for stronger equivalences (e.g. contextual/observational
  equivalence, compiler full abstraction). Hardest of the core techniques; learn it once
  you're solid on the rest.
- **Syntactic type soundness** (progress + preservation).
- **Well-founded recursion / termination** for interpreters and fixpoint computations —
  doc 02 of this very branch is your reference example; you *will* keep meeting this.
- **Abstract interpretation / dataflow** (your specialization — drill the pieces, not just
  the umbrella):
  - **Lattices and fixpoint iteration** — building lattice instances, proving the laws,
    Kleene iteration to a fixpoint (this branch, doc 02).
  - **Galois connections** (`α ⊣ γ`) — this branch used only `γ` (the lighter
    "concretization-only" soundness); learn the full connection, the workhorse of AI design.
  - **Soundness via concretization / post-fixpoints** — `γ` of a sound abstract result is a
    concrete post-fixpoint, hence above the collecting semantics (doc 02 §2.3). This *is*
    the soundness pattern; internalize it.
  - **Widening & narrowing** — the technique this branch *skips* via finite height; the one
    you must add for infinite-height domains. Drill it on intervals.
  - **Domain construction** — non-relational (constants, intervals, congruences) vs
    relational (octagons, polyhedra); product/reduced-product combinators.
  - **MOP vs MFP** — meet-over-all-paths vs the computed maximal-fixpoint solution, and the
    distributivity condition under which they coincide.
  - **Forward vs backward** analyses, and how the framework is reused for both.
- **Metaprogramming for domain automation** — once a proof pattern recurs 5+ times in your
  project, write a tactic for it. PhD-scale verification without custom automation is
  needlessly painful.

### Project-scale skills (the stuff nobody warns you about)

By year 2 these matter more than tactic tricks:
- **Proof performance.** Large proofs get slow. Learn `set_option trace.profiler true`,
  `count_heartbeats`, and `set_option maxHeartbeats`; keep `simp` calls tight (`simp only`),
  and modularize so a change doesn't rebuild the world.
- **Project architecture.** Stable *definitions* and *interfaces* first; isolate the
  spec (doc 08's lesson — the spec is the hard, load-bearing part) from the implementation;
  keep a layered import DAG.
- **Statements before proofs.** Write the theorem, `sorry` it, build the *scaffolding* (all
  the statements and how they compose), get the architecture right, *then* fill proofs.
  Discovering at proof-time that your statement was wrong is the most expensive mistake.
- **Community as infrastructure.** Be active on the **Lean Zulip** (#lean4, #mathlib4, and
  any PL/compiler stream). Post minimal reproductions; answer easier questions than yours
  (teaching). Maintainers and researchers there *are* the expert feedback loop.

### A realistic arc

- **Months 0–3:** Lean fluency (NNG → Macbeth), functional-programming fluency (AoC/Euler),
  and the stack-machine compiler project. Daily cadence locked in.
- **Months 3–12:** Concrete Semantics + Software Foundations PLF *in Lean*; first
  Batteries/Mathlib contributions; start reading CompCert. Drill the core techniques.
- **Year 2:** project-scale skills, CPDT-style automation, your first real research
  formalization; logical relations if your topic needs them.
- **Years 3–5:** you're doing original verification; the "training" is now mostly *reading
  expert proofs in your area*, *building reusable infrastructure*, and *writing/teaching*.
  Mastery shows up as: you predict goal states, you reach for the right technique without
  searching, and you spend your time on the *math and the spec*, not fighting the encoding.

**The throughline:** expertise here is earned in stuck→unstuck cycles, accumulated over
years, with deliberate difficulty selection and honest reflection. Lean's instant feedback
makes those cycles cheap — run as many as you can, write down what each one taught you, and
in a few years you'll be the person answering on Zulip.
