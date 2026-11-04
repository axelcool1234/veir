module

public import Veir.Pass
import Veir.Interfaces.ControlFlowInterfaces
import Veir.Passes.Matching.LLVM.Basic
import Veir.Rewriter.WfRewriter

/-!
# Simple LLVM loop unrolling

This pass unrolls a deliberately narrow class of LLVM CFG loops by a configurable factor. It
accepts a single block loop with one preheader, one backedge, an `iv += 1` induction variable, an
`eq`/`ne` exit test, and a positive constant trip count. Unsupported loops are left unchanged.

The implementation proceeds in four stages:

1. Find blocks whose final `llvm.cond_br` has one self-edge and one exit edge.
2. Refine that structural candidate into a counted loop with a known preheader, induction
   variable, constant trip count, and clonable body.
3. Peel any remainder iterations into the preheader so the residual loop count is divisible by the
   requested unroll factor.
4. Keep the original body as the first iteration, clone the remaining iterations, and reconnect
   loop-carried and live-out SSA values through a value map.

Each matching function is deliberately conservative. A loop that does not satisfy an expected
invariant is ignored rather than partially rewritten.
-/

namespace Veir
namespace LoopUnroll

/-! ## Loop descriptions and structural discovery -/

/--
The outer CFG shape of a possible single-block loop.

This records only facts visible from the header terminator. Later matchers establish the
preheader, body, induction variable, and trip count before any rewriting takes place.
-/
structure Candidate where
  /-- The block containing both the loop body and its backedge terminator. -/
  header : BlockPtr
  /-- The header's final `llvm.cond_br`. -/
  terminator : OperationPtr
  /-- The successor index of `terminator` that points back to `header`. -/
  backedgeIndex : Nat
  /-- The successor index of `terminator` that leaves the loop. -/
  exitIndex : Nat
deriving Repr

/--
A structural candidate refined with every fact needed by the unrolling rewrite.

Arrays describing loop-carried state use the same ordering as `headerArguments`. This lets the
cloner treat an iteration as a state transition from one array of SSA values to the next.
-/
structure CountedLoop where
  /-- The header, terminator, and successor indices found during structural discovery. -/
  candidate : Candidate
  /-- Header operations in program order, excluding the terminator. -/
  body : Array OperationPtr
  /-- Header block arguments representing the state at the start of an iteration. -/
  headerArguments : Array ValuePtr
  /-- The unique `llvm.br` entering the header from outside the loop. -/
  preheaderBranch : OperationPtr
  /-- Values forwarded by `preheaderBranch`, aligned with `headerArguments`. -/
  initialOperands : Array ValuePtr
  /-- Values forwarded along the backedge, aligned with `headerArguments`. -/
  backedgeOperands : Array ValuePtr
  /-- Direct exit-block uses paired with the original body result that they consume. -/
  externalUses : Array (OpOperandPtr × ValuePtr)
  /-- The `llvm.icmp` controlling whether execution follows the backedge. -/
  conditionOp : OperationPtr
  /-- The statically known number of logical iterations before unrolling. -/
  tripCount : Nat
deriving Repr

/--
Recognize whether `header` has the outer CFG shape of a single-block loop.

The backedge can be either successor of `llvm.cond_br`; LLVM transformations may invert the
condition and swap the successors. This matcher intentionally says nothing about the loop body or
induction variable; it only classifies the two outgoing edges.
-/
def matchCandidate? (ctx : IRContext OpCode) (header : BlockPtr) : Option Candidate := do
  -- A candidate loop must end in a conditional branch.
  let some terminator := header.getLastOp! ctx | none
  guard (terminator.getOpType! ctx = .llvm .cond_br)

  -- `llvm.cond_br` has exactly two destinations. One must be a self-edge and the other an exit.
  let successors := terminator.getSuccessors! ctx
  guard (successors.size = 2)
  let some first := successors[0]? | none
  let some second := successors[1]? | none

  -- Preserve the actual successor indices because the branch may have been inverted.
  if first = header ∧ second ≠ header then
    return {
      header
      terminator
      backedgeIndex := 0
      exitIndex := 1
    }
  if second = header ∧ first ≠ header then
    return {
      header
      terminator
      backedgeIndex := 1
      exitIndex := 0
    }
  none

/-- Find every block that has the outer CFG shape recognized by `matchCandidate?`. -/
def findCandidates (ctx : WfIRContext OpCode) : Array Candidate := Id.run do
  let mut candidates := #[]
  -- Blocks store their final operation directly, so discovery visits blocks rather than all ops.
  for block in ctx.raw.blocks.keys do
    if let some candidate := matchCandidate? ctx.raw block then
      candidates := candidates.push candidate
  return candidates

/--
Materialize the candidate's body operations in program order, stopping before the terminator.

VeIR stores block operations as a linked list. Building this array is linear in the body size, but
the rewrite will traverse it several times, so collecting it once avoids repeated linked-list
walks.
-/
def collectBody (ctx : IRContext OpCode) (candidate : Candidate) : Array OperationPtr := Id.run do
  let mut current := candidate.header.getFirstOp! ctx
  let mut body := #[]
  -- `matchCandidate?` obtained the terminator from `getLastOp!`, so it must end this chain.
  while let some op := current do
    if op = candidate.terminator then
      return body
    body := body.push op
    current := op.getNextOp! ctx
  return body

/--
Collect the owner operation of every CFG edge targeting `header`.

A block's use-list is its predecessor-edge list: every `BlockOperandPtr` is owned by the branch
operation that names the block as a successor.
-/
def predecessorOps (ctx : IRContext OpCode) (header : BlockPtr) : Array OperationPtr := Id.run do
  let mut predecessors := #[]
  let mut current := header.getFirstUse! ctx
  -- Follow the block def-use chain instead of scanning every branch in the context.
  while let some blockOperand := current do
    current := blockOperand.getNextUse! ctx
    predecessors := predecessors.push (blockOperand.getOwner! ctx)
  return predecessors

/-! ## Refining a candidate into a counted loop -/

/--
Match the unique non-backedge `llvm.br` entering the header and return its initial loop values.

The supported loop has exactly two incoming edges: the terminator's self-edge and one unconditional
entry edge from a distinct preheader block. Requiring the entry branch to terminate its block gives
the peeling rewrite a stable insertion point.
-/
def matchPreheaderOperands? (ctx : IRContext OpCode) (candidate : Candidate) :
    Option (OperationPtr × Array ValuePtr) := do
  -- Separate the one self-edge from all edges entering the header from outside the loop.
  -- Candidate matching and the well-formed use-list already guarantee exactly one self-edge.
  let predecessors := predecessorOps ctx candidate.header
  let entryEdges := predecessors.filter fun op => op ≠ candidate.terminator
  guard (entryEdges.size = 1)

  -- The external edge must be a simple unconditional branch from a distinct preheader.
  let preheaderBranch := entryEdges[0]!
  guard (preheaderBranch.getOpType! ctx = .llvm .br)
  guard (preheaderBranch.getSuccessors! ctx = #[candidate.header])
  let some preheader := preheaderBranch.getParent! ctx | none
  -- This final llvm.br cannot belong to the header, whose final operation is llvm.cond_br.
  guard (preheader.getLastOp! ctx = some preheaderBranch)

  -- These forwarded operands are the initial values of the header block arguments.
  let operands ← BranchOpInterface.getSuccessorOperands? preheaderBranch 0 ctx
  return (preheaderBranch, operands.forwardedOperands)

/-- Match `value` as one of `header`'s block arguments and return its state-array index. -/
def matchHeaderArgument? (header : BlockPtr) (value : ValuePtr) : Option Nat := do
  let .blockArgument argument := value | none
  guard (argument.block = header)
  return argument.index

/--
Match `value` as `headerArgument + 1`, allowing either operand order, and return the argument index.

Restricting the step to positive one keeps trip-count calculation and remainder peeling simple.
-/
def matchIncrement? (ctx : IRContext OpCode) (header : BlockPtr) (value : ValuePtr) :
    Option Nat := do
  -- The increment must be produced by an operation inside the loop header.
  let .opResult result := value | none
  guard (result.op.getParent! ctx = some header)

  -- Match an LLVM add and identify which side is the loop argument and which side is constant one.
  -- matchAdd requires one result; a well-formed reference to it therefore has index zero.
  let (lhs, rhs, _) ← matchAdd result.op ctx
  if matchConstantIntVal rhs ctx = some 1 then
    matchHeaderArgument? header lhs
  else if matchConstantIntVal lhs ctx = some 1 then
    matchHeaderArgument? header rhs
  else
    none

/--
Match the canonical induction-variable update and return the comparison operation and trip count.

The accepted shape compares `headerArgument + 1` against a constant bound. The branch continues
on `ne` when the backedge is the true successor, or on `eq`'s false result when the backedge is the
false successor. Initial value and bound must both be constants, producing a positive trip count.
-/
def matchInduction? (ctx : IRContext OpCode) (candidate : Candidate)
    (initialOperands backedgeOperands : Array ValuePtr) : Option (OperationPtr × Nat) := do
  -- Operand zero of `llvm.cond_br` is the i1 condition produced by an in-header comparison.
  let some condition := (candidate.terminator.getOperands! ctx)[0]? | none
  let .opResult conditionResult := condition | none
  guard (conditionResult.op.getParent! ctx = some candidate.header)

  -- Account for either branch orientation while requiring the supported equality predicates.
  -- matchIcmp requires one result, so the condition's result index is already known to be zero.
  let (lhs, rhs, properties) ← matchIcmp conditionResult.op ctx
  let continuesOnTrue := candidate.backedgeIndex = 0 ∧ properties.predicate = .ne
  let continuesOnFalse := candidate.backedgeIndex = 1 ∧ properties.predicate = .eq
  guard (continuesOnTrue ∨ continuesOnFalse)

  -- The increment and constant bound may appear on either side of the comparison.
  let (increment, inductionIndex, bound) ←
    (do
      let index ← matchIncrement? ctx candidate.header lhs
      let bound ← matchConstantIntVal rhs ctx
      return (lhs, index, bound)) <|>
    (do
      let index ← matchIncrement? ctx candidate.header rhs
      let bound ← matchConstantIntVal lhs ctx
      return (rhs, index, bound))

  -- The incremented value must be the value carried to the next iteration at the same state index.
  guard (backedgeOperands[inductionIndex]? = some increment)

  -- Recover the matching constant entry value and compute the number of +1 steps to the bound.
  let some initialOperand := initialOperands[inductionIndex]? | none
  let initial ← matchConstantIntVal initialOperand ctx
  let tripCount := bound - initial
  guard (0 ≤ initial)
  guard (0 < tripCount)
  return (conditionResult.op, tripCount.toNat)

/--
Whether every body operation can be cloned linearly without recursively cloning regions or CFG.

Loads, stores, calls, and other regionless operations are allowed. Terminators and operations with
successors are excluded because `unrollByFactor` reconstructs control flow separately.
-/
def isClonableBody (ctx : IRContext OpCode) (body : Array OperationPtr) : Bool :=
  body.all fun op =>
    op.getNumRegions! ctx == 0 && op.getNumSuccessors! ctx == 0 &&
      !HasOpInfo.isTerminator (op.getOpType! ctx)

/--
Collect direct uses of body results in the immediate exit block. Such uses observe the value from
the final logical iteration, so they can be replaced with the corresponding result of the final
clone. Uses in other blocks are rejected because this pass does not analyze dominance or the
surrounding CFG.
-/
def collectExternalUses? (ctx : IRContext OpCode) (candidate : Candidate)
    (body : Array OperationPtr) : Option (Array (OpOperandPtr × ValuePtr)) := Id.run do
  -- Resolve the non-backedge successor once; all accepted live-out uses must be in this block.
  let exitBlock := candidate.terminator.getSuccessor! ctx candidate.exitIndex
  let mut uses := #[]

  -- Start from body results and follow their SSA use-lists, avoiding a scan of unrelated ops.
  for op in body do
    for result in op.getResults! ctx do
      let mut current := result.getFirstUse! ctx
      while let some use := current do
        current := use.getNextUse! ctx
        let userBlock := (use.getOwner! ctx).getParent! ctx

        -- Header uses are internal loop dependencies. Direct exit uses need a final-clone rewrite.
        if userBlock ≠ some candidate.header then
          if userBlock = some exitBlock then
            uses := uses.push (use, result)
          else
            -- Farther uses require CFG and dominance reasoning that this pass does not perform.
            return none
  return some uses

/--
Refine a structural candidate into the conservative counted-loop subset supported by this pass.

This function is the boundary between recognition and rewriting. Once it returns a `CountedLoop`,
the rewrite may rely on aligned state arrays, a clonable body, one preheader, and a constant trip
count. Every failed check simply leaves the candidate unchanged.
-/
def matchCountedLoop? (ctx : IRContext OpCode) (candidate : Candidate) : Option CountedLoop := do
  -- First establish that the linear body is safe to clone operation by operation. The induction
  -- matcher below requires in-header operations, so a successful match implies a nonempty body.
  let body := collectBody ctx candidate
  guard (isClonableBody ctx body)

  -- Record the small class of live-out SSA uses that the rewrite knows how to update.
  let externalUses ← collectExternalUses? ctx candidate body

  -- Read the values carried around the backedge and require one per header block argument.
  let headerArguments := candidate.header.getArguments! ctx
  let backedge ← BranchOpInterface.getSuccessorOperands?
    candidate.terminator candidate.backedgeIndex ctx
  let backedgeOperands := backedge.forwardedOperands
  guard (backedgeOperands.size = headerArguments.size)

  -- Read the matching entry state from the unique preheader and require the same state shape.
  let (preheaderBranch, initialOperands) ← matchPreheaderOperands? ctx candidate
  guard (initialOperands.size = headerArguments.size)

  -- Finally identify which state slot is the induction variable and compute its trip count.
  let (conditionOp, tripCount) ←
    matchInduction? ctx candidate initialOperands backedgeOperands
  return {
    candidate, body, headerArguments, preheaderBranch, initialOperands, backedgeOperands,
      externalUses, conditionOp, tripCount
  }

/-! ## Cloning iterations and reconnecting SSA values -/

/-- Look up an SSA value in the clone map, leaving external values unchanged. -/
def remapValue (mapping : Std.HashMap ValuePtr ValuePtr) (value : ValuePtr) : ValuePtr :=
  (mapping.get? value).getD value

/--
Clone a regionless operation immediately before `before`, preserving its structural metadata.

The caller supplies already-remapped operands. Results are recreated with the same types, while
properties and attributes are copied verbatim so LLVM flags and other dialect data survive
unrolling.
-/
def cloneBefore (ctx : WfIRContext OpCode) (op before : OperationPtr)
    (operands : Array ValuePtr) : Except String (WfIRContext OpCode × OperationPtr) := do
  -- Snapshot everything needed to recreate the source operation.
  let opType := op.getOpType! ctx.raw
  let resultTypes := op.getResultTypes! ctx.raw
  let successors := op.getSuccessors! ctx.raw
  let properties := op.getProperties! ctx.raw opType
  let attributes := op.getAttributes! ctx.raw

  -- Create the clone at its final program position, then restore its attribute dictionary.
  let some (ctx, clone) := WfRewriter.createOp! ctx opType resultTypes operands successors #[]
      properties (some (.before before))
    | throw "loop-unroll: failed to clone an operation"
  return (WfRewriter.setAttributes! ctx clone attributes, clone)

/--
Clone one logical loop iteration from `state` immediately before `before`.

`state[i]` is the value of `headerArguments[i]` at the start of this iteration. The clone map is
seeded with that correspondence, then extended in body order as each original result gains a
cloned result. Applying the completed map to the original backedge operands computes the state for
the following logical iteration.
-/
def cloneIteration (ctx : WfIRContext OpCode) (loop : CountedLoop) (before : OperationPtr)
    (state : Array ValuePtr) : Except String
      (WfIRContext OpCode × Std.HashMap ValuePtr ValuePtr × Array ValuePtr) := do
  -- State arrays and header arguments must remain positionally aligned.
  if state.size ≠ loop.headerArguments.size then
    throw "loop-unroll: loop state has the wrong number of values"
  let mut ctx := ctx
  let mut mapping : Std.HashMap ValuePtr ValuePtr :=
    Std.HashMap.emptyWithCapacity (loop.headerArguments.size + loop.body.size)

  -- Seed the map so body operands that read block arguments consume this iteration's state.
  for (argument, index) in loop.headerArguments.zipIdx do
    mapping := mapping.insert argument state[index]!

  -- Clone in program order so each operation can consume results cloned earlier in the iteration.
  for op in loop.body do
    let operands := (op.getOperands! ctx.raw).map (remapValue mapping)
    let (nextCtx, clone) ← cloneBefore ctx op before operands
    ctx := nextCtx
    -- Record every result pair for later operations, live-outs, and backedge state.
    for index in List.range (op.getNumResults! ctx.raw) do
      mapping := mapping.insert (op.getResult index) (clone.getResult index)

  -- Remapping the original backedge operands yields the values entering the next iteration.
  let nextState := loop.backedgeOperands.map (remapValue mapping)
  return (ctx, mapping, nextState)

/--
Peel `count` iterations into the unique loop preheader.

For a trip count not divisible by the factor, peeling the remainder first leaves a residual loop
whose iterations can be grouped evenly. Each peeled iteration is inserted before the preheader
branch and advances the state that branch will eventually pass to the loop header.
-/
def peelIterations (ctx : WfIRContext OpCode) (loop : CountedLoop) (count : Nat) :
    Except String (WfIRContext OpCode) := do
  -- Avoid rebuilding an identical preheader branch when there is no remainder.
  if count = 0 then return ctx
  let mut ctx := ctx
  let mut state := loop.initialOperands

  -- Materialize the remainder iterations in sequence, threading their loop-carried state.
  for _ in List.range count do
    let (nextCtx, mapping, nextState) ← cloneIteration ctx loop loop.preheaderBranch state
    ctx := nextCtx

    -- A peeled iteration does not branch, so its cloned comparison is usually dead. Keep it only
    -- when it participates in loop-carried state or another cloned operation still uses it.
    if let some clonedCondition := mapping.get? (loop.conditionOp.getResult 0) then
      if !nextState.contains clonedCondition then
        if let .opResult result := clonedCondition then
          if !result.op.hasUses! ctx.raw then
            ctx := WfRewriter.eraseOp! ctx result.op
    state := nextState

  -- Replace the old preheader branch with one forwarding the state after all peeled iterations.
  let (ctxAfterBranch, _) ←
    cloneBefore ctx loop.preheaderBranch loop.preheaderBranch state
  return WfRewriter.eraseOp! ctxAfterBranch loop.preheaderBranch

/--
Unroll `loop` into groups of `factor` logical iterations.

The existing body is retained as the first iteration in each group. Starting from its backedge
state, the rewrite inserts `factor - 1` clones before the old terminator. The final clone map then
identifies the values that must leave the group, either through direct exit-block uses or through
the rebuilt branch operands.
-/
def unrollByFactor (ctx : WfIRContext OpCode) (loop : CountedLoop) (factor : Nat) :
    Except String (WfIRContext OpCode) := do
  let terminator := loop.candidate.terminator

  -- Move the non-divisible prefix into the preheader before changing the residual loop body.
  let remainder := loop.tripCount % factor
  let mut ctx ← peelIterations ctx loop remainder

  -- The original body supplies iteration one; begin cloning from the state on its backedge.
  let mut finalMapping : Std.HashMap ValuePtr ValuePtr :=
    Std.HashMap.emptyWithCapacity (loop.headerArguments.size + loop.body.size)
  let mut state := loop.backedgeOperands
  for _ in List.range (factor - 1) do
    let (nextCtx, mapping, nextState) ← cloneIteration ctx loop terminator state
    ctx := nextCtx
    finalMapping := mapping
    state := nextState

  -- Direct uses in the immediate exit block must observe the last iteration in the group.
  for (use, oldValue) in loop.externalUses do
    let some newValue := finalMapping.get? oldValue
      | throw "loop-unroll: missing clone for an exit block use"
    ctx := WfRewriter.replaceOperand! ctx use newValue

  -- Rebuild the branch with the final condition and loop-carried values, preserving its targets.
  let branchOperands := (terminator.getOperands! ctx.raw).map (remapValue finalMapping)
  let (ctxAfterBranch, _) ← cloneBefore ctx terminator terminator branchOperands
  ctx := WfRewriter.eraseOp! ctxAfterBranch terminator

  -- The original comparison is normally made dead by replacing the terminator; erase it if so.
  if loop.conditionOp.InBounds ctx.raw && !loop.conditionOp.hasUses! ctx.raw then
    ctx := WfRewriter.eraseOp! ctx loop.conditionOp
  return ctx

/-! ## Pass driver -/

/--
Discover candidate loops, refine supported ones, and unroll them independently.

Candidate discovery happens before rewriting so the context is scanned only once. Earlier rewrites
may invalidate pointers held by later candidates, so each terminator is checked again before its
candidate is inspected.
-/
def LoopUnrollPass.impl (options : PassOptions) (ctx : WfIRContext OpCode)
    (_root : OperationPtr) (_ : _root.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  -- A factor below two would not unroll anything and would violate assumptions in the rewrite.
  let factor := (options.getNat? "factor").getD 2
  if factor < 2 then
    throw "factor must be at least 2"

  -- Take a structural snapshot, then progressively rewrite the well-formed context.
  let candidates := findCandidates ctx
  let mut ctx := ctx
  let mut unrolled := 0
  for candidate in candidates do
    -- Skip a candidate erased as a side effect of rewriting an earlier loop.
    if candidate.terminator.InBounds ctx.raw then
      -- Re-run all semantic and structural checks against the current context.
      if let some loop := matchCountedLoop? ctx.raw candidate then
        -- A factor larger than the trip count would eliminate the residual loop, which this simple
        -- pass does not attempt to do.
        if loop.tripCount < factor then continue
        -- Rewrite one loop and thread the resulting well-formed context to the next candidate.
        match unrollByFactor ctx loop factor with
        | .ok nextCtx =>
          ctx := nextCtx
          unrolled := unrolled + 1
        | .error message => throw message

  -- Optional diagnostics are useful in lit tests without changing the transformed IR stream.
  if (options.getBool? "print-candidates").getD false then
    IO.eprintln s!"loop-unroll: unrolled {unrolled} of {candidates.size} CFG candidate(s)"
  return ctx

end LoopUnroll

/-- The configurable single-block LLVM CFG loop-unrolling pass. -/
public def LoopUnrollPass : Pass OpCode :=
  { name := "loop-unroll"
    description := "Unroll supported single-block LLVM CFG loops by a configurable factor."
    options := Std.HashMap.ofList [
      ("factor", {
        description := "Number of loop iterations in each unrolled group."
        defaultValue := .nat 2
      }),
      ("print-candidates", {
        description := "Print the loop discovery and rewrite summary."
      })
    ]
    run := LoopUnroll.LoopUnrollPass.impl }

end Veir
