module

public import Veir.Analysis.DataFlowFramework
public import Std.Data.HashSet
public import Std.Data.HashMap

public section

namespace Veir

open Std (HashMap HashSet)

structure DominatorState extends AnalysisStateHeader where
  iDom : Option BlockPtr := none
deriving TypeName

instance : AnalysisState DominatorState where
  typeNameInst := inferInstance
  mkState := fun anchor =>
    { anchor := anchor
      dependents := #[]
      iDom := none }
  onUpdate (state : DominatorState) (dfCtx : DataFlowContext)
      (_irCtx : IRContext OpCode) : DataFlowContext :=
    { dfCtx with workList := state.enqueueDependents dfCtx.workList }
  toHeader := DominatorState.toAnalysisStateHeader

/-- Hack to cache the post ordering of a region's blocks so we don't
have to recompute it. Stored in the entry block of each region.
-/
structure RegionMetadataState extends AnalysisStateHeader where
  postOrderIndex : HashMap BlockPtr Nat := {}
deriving TypeName

instance : AnalysisState RegionMetadataState where
  typeNameInst := inferInstance
  mkState := fun anchor =>
    { anchor := anchor
      dependents := #[]
      postOrderIndex := {} }
  onUpdate (_state : RegionMetadataState) (dfCtx : DataFlowContext)
      (_irCtx : IRContext OpCode) : DataFlowContext :=
    dfCtx
  toHeader := RegionMetadataState.toAnalysisStateHeader

namespace DominatorState

def get? (block : BlockPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option DominatorState :=
  dfCtx.getState? (.ProgramPoint (ProgramPoint.beforeBlock block irCtx))

/--
Get the immediate dominator for a block. 
-/
def getIDom? (block : BlockPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option BlockPtr :=
  match get? block dfCtx irCtx with
  | some state =>
    state.iDom
  | none =>
    none

/--
Walk up the dominator tree via iDoms to gather the dominators for a block. 
-/
def getDoms? (block : BlockPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option (HashSet BlockPtr) :=
  match get? block dfCtx irCtx with
  | none =>
    none
  | some state =>
    Id.run do
      let mut doms : HashSet BlockPtr := (∅ : HashSet BlockPtr).insert block
      let mut current := state.iDom
      while current.isSome do
        let dom := current.get!
        if dom == block then
          return some doms
        doms := doms.insert dom
        let next := getIDom? dom dfCtx irCtx
        if next == some dom then
          return some doms
        current := next
      some doms

end DominatorState

namespace RegionMetadataState

def get? (dfCtx : DataFlowContext) (region : RegionPtr)
    (irCtx : IRContext OpCode) : Option RegionMetadataState :=
  match (region.get! irCtx).firstBlock with
  | some entry =>
    dfCtx.getState? (.ProgramPoint (ProgramPoint.beforeBlock entry irCtx))
  | none =>
    none

end RegionMetadataState

namespace DominanceAnalysis

def id : Lean.Name :=
  Lean.Name.mkSimple "DominanceAnalysis"

/--
Get the lattice anchor of a given block. 
-/
private def blockEntryAnchor (block : BlockPtr) (irCtx : IRContext OpCode) : LatticeAnchor :=
  .ProgramPoint (ProgramPoint.beforeBlock block irCtx)

/--
Get the successors of a given block. 
-/
private def successorsInRegion
    (block : BlockPtr)
    (region : RegionPtr)
    (irCtx : IRContext OpCode) : Array BlockPtr :=
  match (block.get! irCtx).lastOp with
  | none =>
    #[]
  | some term =>
    Id.run do
      let mut succs := #[]
      for i in [0:term.getNumSuccessors! irCtx] do
        let succ := term.getSuccessor! irCtx i
        if (succ.get! irCtx).parent == some region then
          succs := succs.push succ
      succs

/--
The returned array is CFG in postorder, and the map assigns 
each block a postorder index used by `intersect`.
-/
private def collectPostOrder
    (region : RegionPtr)
    (irCtx : IRContext OpCode) : Array BlockPtr × HashMap BlockPtr Nat :=
  match (region.get! irCtx).firstBlock with
  | none =>
    (#[], {})
  | some entry =>
    Id.run do
      let mut worklist : Array (BlockPtr × Bool) := #[(entry, false)]
      let mut seen : HashSet BlockPtr := ∅
      let mut postOrder : Array BlockPtr := #[]
      let mut postOrderIndex : HashMap BlockPtr Nat := {}

      while !worklist.isEmpty do
        let (block, visited) := worklist.back!
        worklist := worklist.pop

        if visited then
          let index := postOrder.size
          postOrder := postOrder.push block
          postOrderIndex := postOrderIndex.insert block index
        else if seen.contains block then
          continue
        else
          seen := seen.insert block
          worklist := worklist.push (block, true)

          for succ in successorsInRegion block region irCtx do
            if !seen.contains succ then
              worklist := worklist.push (succ, false)
      (postOrder, postOrderIndex)

/- Initialize the dominators in post order and enqueue them in 
reverse post order.
-/
private def initializeRegion
    (region : RegionPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  match (region.get! irCtx).firstBlock with
  | none =>
    dfCtx
  | some entry =>
    Id.run do
      -- Calculate the post order of the blocks and cache it.
      let (postOrder, postOrderIndex) := collectPostOrder region irCtx
      let reversePostOrder := postOrder.reverse
      let metadata : RegionMetadataState :=
        { anchor := blockEntryAnchor entry irCtx
          dependents := #[]
          postOrderIndex := postOrderIndex }
      let mut dfCtx := DataFlowContext.setState dfCtx (blockEntryAnchor entry irCtx) (fun _ => metadata)

      -- Initialize the blocks in post order.
      for block in postOrder do
        let mut dependents := #[]
        for succ in successorsInRegion block region irCtx do
          dependents := dependents.push (ProgramPoint.beforeBlock succ irCtx, id)
        let state : DominatorState :=
          { anchor := blockEntryAnchor block irCtx
            dependents := dependents
            iDom := if block == entry then some entry else none }
        dfCtx := DataFlowContext.setState dfCtx (blockEntryAnchor block irCtx) (fun _ => state)

      -- Enqueue the blocks in reverse post order.
      for block in reversePostOrder do
        match blockEntryAnchor block irCtx with
        | .ProgramPoint point =>
          dfCtx := { dfCtx with workList := dfCtx.workList.enqueue (point, id) }
        | _ =>
          unreachable!

      dfCtx

/--
Recursively initialize the analysis on nested regions.
-/
partial def initializeRecursively
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx

  for i in [0:op.getNumRegions! irCtx] do
    let region := op.getRegion! irCtx i
    dfCtx := initializeRegion region dfCtx irCtx

    let regionData := region.get! irCtx

    let mut maybeBlock := regionData.firstBlock
    while hBlock : maybeBlock.isSome do
      let block := maybeBlock.get hBlock
      let mut maybeOp := (block.get! irCtx).firstOp
      while hOp : maybeOp.isSome do
        let nestedOp := maybeOp.get hOp
        dfCtx := initializeRecursively nestedOp dfCtx irCtx
        maybeOp := (nestedOp.get! irCtx).next
      maybeBlock := (block.get! irCtx).next

  dfCtx

def init
    (top : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  initializeRecursively top dfCtx irCtx


/--
Find the nearest common dominator of `block1` and `block2`.

On each step, the cursor with the smaller postorder index is moved upward
until both cursors coincide. The block where they meet is the nearest common
dominator of the two input blocks.
-/
private def intersect
    (block1 block2 : BlockPtr)
    (postOrderIndex : HashMap BlockPtr Nat)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : BlockPtr := Id.run do
  let mut finger1 := block1
  let mut finger2 := block2
  while finger1 != finger2 do
    while postOrderIndex[finger1]! < postOrderIndex[finger2]! do
      finger1 := (DominatorState.getIDom? finger1 dfCtx irCtx).get!
    while postOrderIndex[finger2]! < postOrderIndex[finger1]! do
      finger2 := (DominatorState.getIDom? finger2 dfCtx irCtx).get!
  finger1

/--
Compute the next immediate dominator candidate for `block`.

The entry block dominates itself. For every other block, we scan its predecessors, pick the first one
whose dominator state has already been computed, and then repeatedly `intersect` that candidate with each
other processed predecessor. Predecessors whose `iDom` is still unknown are skipped until a later solver
iteration.
-/
private def computeImmediateDominator
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option BlockPtr :=
  let region := ((block.get! irCtx).parent).get!
  let entry := ((region.get! irCtx).firstBlock).get!
  match RegionMetadataState.get? dfCtx region irCtx with
  | none =>
    none
  | some metadata =>
    if block == entry then
      some entry
    else
      Id.run do
        let mut maybePredUse := (block.get! irCtx).firstUse
        let mut newIDom : Option BlockPtr := none

        while hUse : maybePredUse.isSome do
          let predUse := maybePredUse.get hUse
          let predUseStruct := predUse.get! irCtx
          maybePredUse := predUseStruct.nextUse
          let predOp := predUseStruct.owner
          let some predBlock := (predOp.get! irCtx).parent
            | continue
          if (predBlock.get! irCtx).parent != some region then
            continue
          let some _ := DominatorState.getIDom? predBlock dfCtx irCtx
            | continue
          newIDom := match newIDom with
            | none => some predBlock
            | some current => some (intersect predBlock current metadata.postOrderIndex dfCtx irCtx)

        newIDom

def visit
    (point : ProgramPoint)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  if !point.isBlockStart irCtx then
    dfCtx
  else
    let block := (point.getBlock?).get!
    match computeImmediateDominator block dfCtx irCtx with
    | none =>
      dfCtx
    | some newIDom =>
      let anchor := blockEntryAnchor block irCtx
      DataFlowContext.setStateAndUpdate dfCtx anchor (State := DominatorState) (fun oldState =>
        ({ oldState with iDom := some newIDom }, some newIDom != oldState.iDom)) irCtx

/-- Get a block's immediate dominator. -/
def immediateDominator?
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Option BlockPtr :=
  match DominatorState.getIDom? block dfCtx irCtx with
  | some iDom =>
    if iDom == block then none else some iDom
  | none =>
    none

/-- Recurse up the dominator tree to see if `dominator` 
is hit. If it is, then `dominator` dominates `block`.
-/
def dominates
    (dominator block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  if dominator == block then
    (DominatorState.get? block dfCtx irCtx).isSome
  else
    match DominatorState.get? block dfCtx irCtx with
    | none =>
      false
    | some state =>
      Id.run do
        let mut current := state.iDom
        while current.isSome do
          let candidate := current.get!
          if candidate == dominator then
            return true
          let next := DominatorState.getIDom? candidate dfCtx irCtx
          if next == some candidate then
            return false
          current := next
        false

/-- Same thing as `dominates` except a blcok dominating itself
doesn't count.
-/
def strictlyDominates
    (dominator block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  dominator != block && dominates dominator block dfCtx irCtx

end DominanceAnalysis

def DominanceAnalysis : DataFlowAnalysis :=
  DataFlowAnalysis.new
    DominanceAnalysis.id
    DominanceAnalysis.init
    DominanceAnalysis.visit

end Veir
