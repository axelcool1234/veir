module

public import Veir.Analysis.DataFlow.SparseLatticeState
public import Veir.Analysis.DataFlow.DeadCodeAnalysis

public section

namespace Veir

open Std (HashMap)

-- *=============================================================================*
-- |                         DataFlowAnalysis Children                           |
-- *=============================================================================*

-- ======================= SparseForwardDataFlowAnalysis ========================= --
namespace SparseForwardDataFlowAnalysis

variable {Domain : Type}
variable [AnalysisState (SparseLatticeState Domain)] [LatticeElement Domain]

abbrev VisitOperationFn :=
  OperationPtr -> Array ValuePtr -> Array ValuePtr ->
    DataFlowContext -> IRContext OpCode -> DataFlowContext

abbrev SetToEntryStateFn :=
  ValuePtr -> DataFlowContext -> IRContext OpCode -> DataFlowContext

/--
Join a sparse lattice fact into the target value state and propagate updates
when it changes.

This is the generic sparse-analysis primitive that merges an incoming lattice
element into the stored state for an SSA value.
-/
def joinLatticeElement
    (target : ValuePtr)
    (incoming : Domain)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let oldValue := SparseLatticeState.getElementD dfCtx target LatticeElement.bottom
  let newValue := LatticeElement.join oldValue incoming
  if newValue == oldValue then
    return dfCtx
  dfCtx.setStateAndUpdate (.ValuePtr target) (State := SparseLatticeState Domain) (fun oldState =>
    ({ oldState with latticeElement := newValue }, true)) irCtx

/--
Return whether the given operation is a branch op.
-/
private def isBranchOp
    (op : OperationPtr)
    (irCtx : IRContext OpCode) : Bool :=
  -- TODO: Replace this `.test .test` check once VeIR has proper branch ops.
  match (op.get! irCtx).opType with
  | .test .test =>
    true
  | _ =>
    false

/--
Return the SSA values forwarded to the given successor's block arguments.
-/
private def getSuccessorOperands
    (op : OperationPtr)
    (successorIndex : Nat)
    (irCtx : IRContext OpCode) : Array (Option ValuePtr) :=
  if successorIndex >= op.getNumSuccessors! irCtx then
    panic! s!"SparseForwardDataFlowAnalysis.getSuccessorOperands: successor index {successorIndex} out of range"
  else
    match (op.get! irCtx).opType with
    -- TODO: Replace this `.test .test` check once VeIR has proper branch ops.
    | .test .test =>
      Id.run do
        let mut operands : Array (Option ValuePtr) := #[]
        for i in [0:op.getNumOperands! irCtx] do
          operands := operands.push (some (op.getOperand! irCtx i))
        operands
    | _ =>
      panic! "SparseForwardDataFlowAnalysis.getSuccessorOperands: non-branch op"

/--
Set the given lattice element(s) at control flow entry point(s).
-/
def setAllToEntryStates
    (setToEntryState : SetToEntryStateFn)
    (values : Array ValuePtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  for target in values do
    dfCtx := setToEntryState target dfCtx irCtx
  dfCtx

/--
Visit a block during sparse initialization.
-/
private def visitBlock
    (analysisName : Lean.Name)
    (setToEntryState : SetToEntryStateFn)
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- Exit early on blocks with no arguments.
  if block.getNumArguments! irCtx == 0 then
    return dfCtx 

  -- If the block is not executable, bail out.
  let blockPoint := ProgramPoint.beforeBlock block irCtx
  match dfCtx.getState? (State := ExecutableState) (.ProgramPoint blockPoint) with
  | some executableState =>
    if !executableState.live then
      return dfCtx
  | none => -- By default, program point is NOT live (live == false).
    return dfCtx

  -- Get the argument values.
  let argValues : Array ValuePtr := Id.run do
    let mut args := #[]
    for i in [0:block.getNumArguments! irCtx] do
      args := args.push (ValuePtr.blockArgument (block.getArgument i))
    args

  if hParent : (block.get! irCtx).parent.isSome then
    let parentRegion := (block.get! irCtx).parent.get hParent
    -- The argument lattices of entry blocks are set by region control-flow or
    -- the callgraph.
    if (parentRegion.get! irCtx).firstBlock == some block then
      -- TODO: Mirror MLIR's handling of `visitCallableOperation` and
      -- `visitRegionSuccessors` for entry blocks.
      return dfCtx

    let mut dfCtx := dfCtx

    -- Iterate over the predecessors of the non-entry block.
    let mut maybePredUse := (block.get! irCtx).firstUse

    while hUse : maybePredUse.isSome do
      let predUse := maybePredUse.get hUse
      let predUseStruct := predUse.get! irCtx
      maybePredUse := predUseStruct.nextUse

      let predecessorOp := predUseStruct.owner
      let some predecessorBlock := (predecessorOp.get! irCtx).parent
        | continue

      let edgeAnchor : LatticeAnchor := .CFGEdge (predecessorBlock, block)
      dfCtx := dfCtx.setState edgeAnchor (State := ExecutableState) (fun state =>
        state.blockContentSubscribe analysisName)
      let some edgeState := dfCtx.getState? (State := ExecutableState) edgeAnchor
        | panic! "SparseForwardDataFlowAnalysis.visitBlock: missing edge state after setState"

      -- If the edge from the predecessor block to the current block is not live,
      -- bail out.
      if !edgeState.live then
        continue

      -- Check if we can reason about the data-flow from the predecessor.
      if isBranchOp predecessorOp irCtx then
        let successorOperands := getSuccessorOperands predecessorOp predUse.index irCtx
        for i in [0:block.getNumArguments! irCtx] do
          let argValue := argValues[i]!
          match successorOperands[i]? with
          | some (some operand) => 
            -- Add the current block-start program point as a dependency of the
            -- predecessor block's successor-operand lattice state, so this block 
            -- is revisited when that operand lattice changes.
            let dependentPoint := ProgramPoint.beforeBlock block irCtx
            let workItem : WorkItem := (dependentPoint, analysisName)
            dfCtx := dfCtx.setState (.ValuePtr operand) (State := SparseLatticeState Domain) (fun state =>
              if state.dependents.any (fun dependent =>
                  dependent.1 == dependentPoint && dependent.2 == analysisName) then
                -- Do not add dependent again if it's already added.
                state
              else
                { state with dependents := state.dependents.push workItem })
            
            -- Call transfer function
            let incoming : Domain :=
              SparseLatticeState.getElementD (Domain := Domain) dfCtx operand (LatticeElement.bottom : Domain)
            dfCtx := joinLatticeElement argValue incoming dfCtx irCtx
          | _ =>
            -- Conservatively consider internally produced arguments as entry
            -- points.
            dfCtx := setToEntryState argValue dfCtx irCtx
      else
        return setAllToEntryStates setToEntryState argValues dfCtx irCtx

    return dfCtx

  dfCtx 

mutual

/--
Ensure an operand has a sparse lattice state and subscribe the current sparse
analysis to its updates. This is what makes use-def driven revisitation work.
-/
partial def subscribeToOperand
    (analysisName : Lean.Name)
    (operand : ValuePtr)
    (dfCtx : DataFlowContext) : DataFlowContext :=
  dfCtx.setState (.ValuePtr operand) (State := SparseLatticeState Domain) (fun state =>
    SparseLatticeState.useDefSubscribe state analysisName)

/--
Visit one operation in the sparse analysis.
We first subscribe to operand lattices, then hand the operation plus its
operand/result values to the user provided transfer function.
-/
partial def visitOperation
    (analysisName : Lean.Name)
    (visitOperationImpl : VisitOperationFn)
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- Exit early on operations with no results.
  if op.getNumResults! irCtx == 0 then
    return dfCtx

  -- If the containing block is not executable, bail out. Executability is
  -- unreachable until proven live, so a missing state is treated as dead.
  if hParent : (op.get! irCtx).parent.isSome then
    let parentBlock := (op.get! irCtx).parent.get hParent
    let blockPoint := ProgramPoint.beforeBlock parentBlock irCtx
    match dfCtx.getState? (State := ExecutableState) (.ProgramPoint blockPoint) with
    | some executableState =>
      if !executableState.live then
        return dfCtx
    | none =>
      return dfCtx

  -- Get the result values.
  let resultValues : Array ValuePtr := Id.run do
    let mut results := #[]
    for i in [0:op.getNumResults! irCtx] do
      results := results.push (.opResult (op.getResult i))
    results

  -- TODO: Mirror MLIR more closely by `visitRegionSuccessors`
  -- Comment: The results of a region branch operation are determined by control-flow.

  -- Grab the ValuePtrs of the operands.
  let operandValues : Array ValuePtr := Id.run do
    let mut operands := #[]
    for i in [0:op.getNumOperands! irCtx] do
      operands := operands.push (op.getOperand! irCtx i)
    operands

  -- TODO: Mirror MLIR more closely by `visitCallOperation`

  let mut dfCtx := dfCtx
  for operand in operandValues do
    dfCtx := subscribeToOperand analysisName operand dfCtx

  -- Invoke the operation transfer function.
  visitOperationImpl op operandValues resultValues dfCtx irCtx

/--
Recursively initialize an operation tree for sparse analysis.
Visit the current operation first, then walk its nested regions, 
blocks, and nested operations.
-/
partial def initializeRecursively
    (analysisName : Lean.Name)
    (visitOperationImpl : VisitOperationFn)
    (setToEntryState : SetToEntryStateFn)
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- Initialize the analysis by visiting every owner of an SSA value (all
  -- operations and blocks).
  let mut dfCtx := dfCtx
  dfCtx := visitOperation analysisName visitOperationImpl op dfCtx irCtx

  for i in [0:op.getNumRegions! irCtx] do
    let region := (op.getRegion! irCtx i).get! irCtx
    let mut maybeBlock := region.firstBlock

    while h : maybeBlock.isSome do
      let block := maybeBlock.get h
      let blockPoint := ProgramPoint.beforeBlock block irCtx
      dfCtx := dfCtx.setState (.ProgramPoint blockPoint) (State := ExecutableState) (fun state =>
        state.blockContentSubscribe analysisName)
      dfCtx := visitBlock (Domain := Domain) analysisName setToEntryState block dfCtx irCtx
      let mut maybeOp := (block.get! irCtx).firstOp

      while hOp : maybeOp.isSome do
        let nestedOp := maybeOp.get hOp
        dfCtx := initializeRecursively analysisName visitOperationImpl setToEntryState nestedOp dfCtx irCtx
        maybeOp := (nestedOp.get! irCtx).next

      maybeBlock := (block.get! irCtx).next
  dfCtx

end

-- Initialize the analysis by visiting every owner of an SSA value: all
-- operations and blocks.
private def init
    (analysisName : Lean.Name)
    (visitOperationImpl : VisitOperationFn)
    (setToEntryState : SetToEntryStateFn)
    (top : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- Mark the entry block arguments as having reached their pessimistic
  -- fixpoints.
  let mut dfCtx := dfCtx
  for i in [0:top.getNumRegions! irCtx] do
    let region := (top.getRegion! irCtx i).get! irCtx
    if h : region.firstBlock.isSome then
      let firstBlock := region.firstBlock.get h
      for j in [0:firstBlock.getNumArguments! irCtx] do
        let arg := ValuePtr.blockArgument (firstBlock.getArgument j)
        dfCtx := setToEntryState arg dfCtx irCtx

  initializeRecursively (Domain := Domain) analysisName visitOperationImpl setToEntryState top dfCtx irCtx

-- Visit a program point. If this is at beginning of block and all
-- control-flow predecessors or callsites are known, then the arguments
-- lattices are propagated from them. If this is after call operation or an
-- operation with region control-flow, then its result lattices are set
-- accordingly. Otherwise, the operation transfer function is invoked.
private def visit
    (analysisName : Lean.Name)
    (visitOperationImpl : VisitOperationFn)
    (setToEntryState : SetToEntryStateFn)
    (point : ProgramPoint)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  if !point.isBlockStart irCtx then
    visitOperation (Domain := Domain) analysisName visitOperationImpl (point.getPrevOp! irCtx) dfCtx irCtx
  else
    match point.getBlock? with
    | some block =>
      visitBlock (Domain := Domain) analysisName setToEntryState block dfCtx irCtx
    | none =>
      panic! "SparseForwardDataFlowAnalysis.visit: block-start point without block"

-- visitOperationImpl: The operation transfer function. Given the operand lattices, 
-- this function is expected to set the result lattices.
-- setToEntryState: Set the given lattice element(s) at control flow entry point(s).
def new
    (Domain : Type)
    [AnalysisState (SparseLatticeState Domain)]
    [LatticeElement Domain]
    (analysisName : Lean.Name)
    (visitOperationImpl : VisitOperationFn)
    (setToEntryState : SetToEntryStateFn) :
    DataFlowAnalysis :=
  DataFlowAnalysis.new
      analysisName
      (init (Domain := Domain) analysisName visitOperationImpl setToEntryState)
      (visit (Domain := Domain) analysisName visitOperationImpl setToEntryState)

end SparseForwardDataFlowAnalysis

-- =============================================================================== --
end Veir
