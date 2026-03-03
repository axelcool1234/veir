module

public import Veir.Analysis.DataFlow.ConstantDomain
public import Veir.Analysis.DataFlow.SparseLatticeState
public import Veir.Analysis.DataFlowFramework
public import Std.Data.HashSet

public section

namespace Veir

-- *=============================================================================*
-- |                          AnalysisState Children                             |
-- *=============================================================================*

-- ================================= Executable ================================== --
-- This is a simple analysis state that represents whether the associated
-- lattice anchor (either a block or a control-flow edge) is live.
structure ExecutableState extends AnalysisStateHeader where
  live : Bool := false
  subscribers : Array Lean.Name := #[]
deriving TypeName

instance : AnalysisState ExecutableState where
  typeNameInst := inferInstance
  mkState := fun anchor =>
    { anchor := anchor
      dependents := #[]
      live := false
      subscribers := #[] }
  onUpdate (state : ExecutableState) (dfCtx : DataFlowContext)
      (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
    let mut dfCtx := { dfCtx with workList := state.enqueueDependents dfCtx.workList }
    match state.anchor with
    | .ProgramPoint point =>
      if point.isBlockStart irCtx then
        -- Re-invoke the analyses on the block itself.
        for analysisId in state.subscribers do
          dfCtx := { dfCtx with workList := dfCtx.workList.enqueue (point, analysisId) }

        let some block := point.getBlock?
          | panic! "SparseForwardDataFlowAnalysis.visit: block-start point without block"  

        -- Re-invoke the analyses on all operations in the block.
        for analysisId in state.subscribers do
          let mut maybeOp := (block.get! irCtx).firstOp
          while h : maybeOp.isSome do
            let op := maybeOp.get h
            dfCtx := { dfCtx with workList := dfCtx.workList.enqueue (ProgramPoint.afterOp op irCtx, analysisId) }
            maybeOp := (op.get! irCtx).next
    | .CFGEdge edge =>
      -- Re-invoke the analysis on the successor block.
      for analysisId in state.subscribers do
        dfCtx := { dfCtx with workList := dfCtx.workList.enqueue (ProgramPoint.beforeBlock edge.getTo irCtx, analysisId) }
    | _ =>
      pure ()
    dfCtx
  toHeader := ExecutableState.toAnalysisStateHeader

namespace ExecutableState

def setToLive (state : ExecutableState) : ExecutableState :=
  { state with live := true }

def blockContentSubscribe (state : ExecutableState) (analysisId : Lean.Name) : ExecutableState :=
  if state.subscribers.contains analysisId then
    state
  else
    { state with subscribers := state.subscribers.push analysisId }

end ExecutableState
-- =============================================================================== --

-- ============================== PredecessorState  ============================== --
-- This analysis state represents a set of live control-flow "predecessors" of
-- a program point (either an operation or a block), which are the last
-- operations along all execution paths that pass through this point.
-- 
-- For example, in dead-code analysis, an operation with region control-flow
-- can be the predecessor of a region's entry block or itself, the exiting
-- terminator of a region can be the predecessor of the parent operation or
-- another region's entry block, the callsite of a callable operation can be
-- the predecessor to its entry block, and the exiting terminator or a callable
-- operation can be the predecessor of the call operation.
-- 
-- The state can optionally contain information about which values are
-- propagated from each predecessor to the successor point.
-- 
-- The state can indicate that it is underdefined, meaning that not all live
-- control-flow predecessors can be known.
structure PredecessorState extends AnalysisStateHeader where
  -- Whether all predecessors are known. Optimistically assume that we know
  -- all predecessors.
  allKnown : Bool := true

  -- The known control-flow predecessors of this program point.
  knownPredecessors : Std.HashSet OperationPtr := ∅

  -- The successor inputs when branching from a given predecessor.
  successorInputs : Std.HashMap OperationPtr (Array ValuePtr) := ∅
deriving TypeName

instance : AnalysisState PredecessorState where
  typeNameInst := inferInstance
  mkState := fun anchor =>
    { anchor := anchor
      dependents := #[]
      allKnown := true
      knownPredecessors := ∅
      successorInputs := ∅ }
  onUpdate (state : PredecessorState) (dfCtx : DataFlowContext)
      (_irCtx : IRContext OpCode) : DataFlowContext :=
    { dfCtx with workList := state.enqueueDependents dfCtx.workList }
  toHeader := PredecessorState.toAnalysisStateHeader

namespace PredecessorState

def getSuccessorInputs (state : PredecessorState)
    (predecessor : OperationPtr) : Array ValuePtr :=
  state.successorInputs.getD predecessor #[]

/--
Add a known predecessor, optionally recording the successor inputs propagated
from it.
-/
def join (state : PredecessorState) (predecessor : OperationPtr)
    (inputs : Array ValuePtr := #[]) : PredecessorState :=
  let state :=
    { state with knownPredecessors := state.knownPredecessors.insert predecessor }
  if inputs.isEmpty then
    state
  else
    match state.successorInputs.get? predecessor with
    | some currentInputs =>
      if currentInputs == inputs then
        state
      else
        { state with successorInputs := state.successorInputs.insert predecessor inputs }
    | none =>
      { state with successorInputs := state.successorInputs.insert predecessor inputs }

end PredecessorState
-- =============================================================================== --

-- *=============================================================================*
-- |                         DataFlowAnalysis Children                           |
-- *=============================================================================*

-- ============================== DeadCodeAnalysis  ============================== --
namespace DeadCodeAnalysis

def id : Lean.Name :=
  Lean.Name.mkSimple "DeadCodeAnalysis"

/--
Mark the CFG edge from `src` to `dst` as live.
This also marks the destination block entry point as live.
-/
def markEdgeLive
    (src : BlockPtr)
    (dst : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  let point := ProgramPoint.beforeBlock dst irCtx
  dfCtx := dfCtx.setStateAndUpdate (.ProgramPoint point) (State := ExecutableState) (fun state =>
    (state.setToLive, !state.live)) irCtx
  dfCtx := dfCtx.setStateAndUpdate (.CFGEdge (src, dst)) (State := ExecutableState) (fun state =>
    (state.setToLive, !state.live)) irCtx
  dfCtx

/-- Mark the entry blocks of all regions attached to `op` as live. -/
def markEntryBlocksLive
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  for i in [0:op.getNumRegions! irCtx] do
    let region := (op.getRegion! irCtx i).get! irCtx
    if h : region.firstBlock.isSome then
      let block := region.firstBlock.get h
      let point := ProgramPoint.beforeBlock block irCtx
      dfCtx := dfCtx.setStateAndUpdate (.ProgramPoint point) (State := ExecutableState) (fun state =>
        (state.setToLive, !state.live)) irCtx
  dfCtx

/-- Return whether the given operation is a branch op. -/
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
Get the constant domain lattice elements of the operands of an operation.
If any operand lattice is still uninitialized, return `none` to indicate that
dead-code analysis should bail out until sparse constant propagation learns more.
This also subscribes dead code analysis to the operand lattices so the branch is 
revisited when those facts change.
-/
def getOperandValues
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext × Option (Array ConstantDomain) := Id.run do
  let mut dfCtx := dfCtx
  let mut operands : Array ConstantDomain := #[]
  for i in [0:op.getNumOperands! irCtx] do
    let operand := op.getOperand! irCtx i
    dfCtx := dfCtx.setState (.ValuePtr operand) (State := SparseLatticeState ConstantDomain) (fun state =>
      SparseLatticeState.useDefSubscribe state id)
    let latticeElement :=
      SparseLatticeState.getElementD (Domain := ConstantDomain) dfCtx operand ConstantDomain.bottom
    -- If any of the operands' values are uninitialized, bail out.
    if latticeElement == ConstantDomain.bottom then
      return (dfCtx, none)
    operands := operands.push latticeElement
  (dfCtx, some operands)

/--
Returns the successor that would be chosen with the given constant
operands. Returns nullptr if a single successor could not be chosen.

TODO: Replace this once VeIR supports branch operators! For now, we
treat `.test .test` as a branch operator with the following semantics:
- one successor: always take it
- two successors: inspect the first operand as a boolean-like integer,
  taking successor 0 when nonzero and successor 1 when zero
- otherwise: unknown
-/
private def getSuccessorForOperands?
    (op : OperationPtr)
    (operands : Array ConstantDomain)
    (irCtx : IRContext OpCode) : Option BlockPtr :=
  if op.getNumSuccessors! irCtx == 1 then
    some (op.getSuccessor! irCtx 0)
  else if op.getNumSuccessors! irCtx == 2 then
    match operands[0]? with
    | some (ConstantDomain.constant constant) =>
      match constant.value with
      | Data.LLVM.Int.val value =>
        if value == 0 then
          some (op.getSuccessor! irCtx 1)
        else
          some (op.getSuccessor! irCtx 0)
      | Data.LLVM.Int.poison =>
        none
    | _ =>
      none
  else
    none

def visitBranchOperation
    (branch : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- Try to deduce a single successor for the branch.
  let (dfCtx, operands?) := getOperandValues branch dfCtx irCtx
  let some operands := operands?
    | return dfCtx
  let some parentBlock := (branch.get! irCtx).parent
    | return dfCtx

  match getSuccessorForOperands? branch operands irCtx with
  -- Branch has single successor
  | some successor =>
    markEdgeLive parentBlock successor dfCtx irCtx
  -- Branch has multiple/all successors live, so mark all 
  -- successors as executable and outgoing edges.
  | none =>
    let mut dfCtx := dfCtx
    for i in [0:branch.getNumSuccessors! irCtx] do
      let successor := branch.getSuccessor! irCtx i
      dfCtx := markEdgeLive parentBlock successor dfCtx irCtx
    dfCtx

-- Visit an operation with control-flow semantics and deduce which of its
-- successors are live.
def visit
    (point : ProgramPoint)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  if point.isBlockStart irCtx then
    return dfCtx

  let op := point.getPrevOp! irCtx

  -- If the parent block is not executable, there is nothing to do.
  if hParent : (op.get! irCtx).parent.isSome then
    let parentBlock := (op.get! irCtx).parent.get hParent
    let blockPoint := ProgramPoint.beforeBlock parentBlock irCtx
    match dfCtx.getState? (State := ExecutableState) (.ProgramPoint blockPoint) with
    | some executableState =>
      -- If parent block not live, skip op      
      if !executableState.live then
        return dfCtx
    -- liveness is false by default so also return here as the parent block is not executable
    | none => 
      return dfCtx

  let mut dfCtx := dfCtx

  -- TODO: If we have a live call op, add this as a live predecessor of the callee.

  -- Visit the regions.
  if op.getNumRegions! irCtx != 0 then
    -- TODO: Check if we can reason about region control-flow.

    -- TODO: Check if this is a callable operation and use callsite information
    -- to decide whether to mark the callable executable.
    
    -- else:
    dfCtx := markEntryBlocksLive op dfCtx irCtx

  -- TODO: If `op` is a region or callable return, visit the corresponding
  -- terminator semantics once VeIR has the necessary interfaces.

  -- Visit the successors.
  if op.getNumSuccessors! irCtx != 0 then
    if hParent : (op.get! irCtx).parent.isSome then
      let parentBlock := (op.get! irCtx).parent.get hParent

      -- Check if we can reason about the control-flow.
      if isBranchOp op irCtx then
        dfCtx := visitBranchOperation op dfCtx irCtx
      else
        -- Conservatively mark all successors as executable.
        for i in [0:op.getNumSuccessors! irCtx] do
          let successor := op.getSuccessor! irCtx i
          dfCtx := markEdgeLive parentBlock successor dfCtx irCtx
    else
      -- TODO: Handle standalone operations with successors if VeIR ever models them.
      pure ()

  dfCtx

/--
Recursively initialize the analysis on nested regions.
Visit operations that may affect control-flow, subscribe them to
parent-block liveness, then recurse into nested regions.
-/
partial def initializeRecursively
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx

  -- Initialize the analysis by visiting every op with control-flow semantics.
  if op.getNumRegions! irCtx != 0 || op.getNumSuccessors! irCtx != 0 then
    -- TODO: || isRegionOrCallableReturn op || isACallOpInterface op

    -- When the liveness of the parent block changes, make sure to re-invoke
    -- the analysis on the op.
    if h : (op.get! irCtx).parent.isSome then
      let parentBlock := (op.get! irCtx).parent.get h
      let blockPoint := ProgramPoint.beforeBlock parentBlock irCtx
      dfCtx := dfCtx.setState (.ProgramPoint blockPoint) (State := ExecutableState) (fun state =>
        state.blockContentSubscribe id)

    -- Visit the op.
    dfCtx := visit (ProgramPoint.afterOp op irCtx) dfCtx irCtx

  -- Recurse on nested operations.
  for i in [0:op.getNumRegions! irCtx] do
    -- TODO: If we haven't seen a symbol table yet, check if the current operation
    -- has one. If so, update the flag to allow for resolving callables in
    -- nested regions.
    let region := (op.getRegion! irCtx i).get! irCtx
    let mut maybeBlock := region.firstBlock
    while h : maybeBlock.isSome do
      let block := maybeBlock.get h
      let mut maybeOp := (block.get! irCtx).firstOp
      while hOp : maybeOp.isSome do
        let nestedOp := maybeOp.get hOp
        dfCtx := initializeRecursively nestedOp dfCtx irCtx
        maybeOp := (nestedOp.get! irCtx).next
      maybeBlock := (block.get! irCtx).next
  dfCtx

-- Initialize the analysis by visiting every operation with potential
-- control-flow semantics.
def init
    (top : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- Mark the top-level blocks as executable.
  let dfCtx := markEntryBlocksLive top dfCtx irCtx

  -- TODO: Mark as overdefined the predecessors of symbol callables with
  -- potentially unknown predecessors.

  initializeRecursively top dfCtx irCtx

end DeadCodeAnalysis

def DeadCodeAnalysis :=
  DataFlowAnalysis.new
    DeadCodeAnalysis.id
    DeadCodeAnalysis.init
    DeadCodeAnalysis.visit

-- =============================================================================== --

end Veir
