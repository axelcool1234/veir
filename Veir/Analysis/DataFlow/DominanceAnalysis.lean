module

public import Veir.Analysis.DataFlowFramework
public import Veir.Analysis.DataFlow.Domains.DominanceDomain

public section

namespace Veir

open Std (HashMap HashSet)

/-!
# Dominance analysis

This module implements immediate dominator analysis using the Cooper Harvey
Kennedy algorithm described in their paper "A Simple, Fast Dominance Algorithm."

Like the algorithm in that paper, we initialize the entry block to dominate
itself, process reachable blocks in reverse postorder, and iteratively refine
each block's immediate dominator by intersecting the dominator chains of its
already processed predecessors. The `intersect` helper uses dense reverse postorder
indices as pointers into cached immediate dominator chains. The lower ranked
pointer is moved upward until both pointers meet at their nearest common dominator
`computeImmediateDominator` implements the paper's update step by choosing the first
predecessor whose immediate dominator is already known as an initial candidate, then
repeatedly intersects that candidate with the other predecessors whose immediate
dominator is already known. The resulting candidate is the current immediate
dominator estimate for the block. Each reverse postorder sweep either preserves the
estimates or moves them upward in the dominator tree (note that this is monotonic!),
and the process repeats until the facts reach a fixpoint.

In VeIR, one dominance fact attached to the entry block stores the result for an
entire region. It caches the reverse postorder, maps blocks to dense indices, and
stores the immediate dominator and predecessor indices used by `intersect`. A
region's entry point is its dataflow work item. Each visit performs exactly one
complete reverse postorder sweep, then re-enqueues the entry point when another
sweep is required.
-/

namespace RegionPtr

/--
Look up the region dominance fact stored at the entry block of `region`.

Returns `none` when the region has no entry block or when dominance analysis has
not attached a fact to that entry block.
-/
def getRegionDominanceFact? [FactSpec .regionDominance]
    (region : RegionPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Option RegionDominanceFact :=
  (region.get! irCtx.raw).firstBlock >>= dfCtx.getFact? .regionDominance ∘ .BlockPtr

end RegionPtr

namespace BlockPtr

/--
Did the dominance analysis reach `block` from the entry of its enclosing region?

Reachable blocks have an index and an initialized immediate dominator index in
their enclosing region's dominance fact.
-/
def isReachable [FactSpec .regionDominance]
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : Bool := Id.run do
  let some region := (block.get! irCtx.raw).parent
    | return false
  let some dominance := region.getRegionDominanceFact? dfCtx irCtx
    | return false
  let some index := dominance.blockIndex.get? block
    | return false
  return dominance.dominanceValue.get? index |>.isSome

end BlockPtr

namespace RegionDominanceFact

def mkDefault : RegionDominanceFact :=
  { dependents := #[]
    payload := {} }

def propagate (fact : RegionDominanceFact) (_anchor : LatticeAnchor)
    (dfCtx : DataFlowContext) (_irCtx : WfIRContext OpCode) : DataFlowContext :=
  { dfCtx with workList := fact.enqueueDependents dfCtx.workList }

instance : FactSpec .regionDominance where
  mkDefault := RegionDominanceFact.mkDefault
  propagate := RegionDominanceFact.propagate

end RegionDominanceFact

namespace DominanceAnalysis

def kind : AnalysisKind :=
  .dominance

/--
The returned array is the CFG in postorder.
-/
@[expose] def collectPostOrder
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode) : Array BlockPtr := Id.run do
  let mut postOrder : Array BlockPtr := #[]
  let some entry := (region.get! irCtx.raw).firstBlock
    | return postOrder
  let mut stack : List (BlockPtr × Nat) := [(entry, 0)]
  let mut seen : HashSet BlockPtr := ∅
  seen := seen.insert entry

  while !stack.isEmpty do
    let (block, successorIndex) := stack.head!
    let successors := block.getSuccessors! irCtx.raw
    if h : successorIndex < successors.size then
      stack := (block, successorIndex + 1) :: stack.tail
      let successor := successors[successorIndex]
      if !seen.contains successor then
        seen := seen.insert successor
        stack := (successor, 0) :: stack
    else
      stack := stack.tail
      postOrder := postOrder.push block
  postOrder

/-- Add one represented block's outgoing edges to the predecessor table. -/
@[expose, inline] def addPredecessorEdges
    (predecessors : Array (Array Nat))
    (predecessorIndex : Nat)
    (successors : Array BlockPtr)
    (blockIndex : HashMap BlockPtr Nat) : Array (Array Nat) := Id.run do
  let mut predecessors := predecessors
  for block in successors do
    let some index := blockIndex.get? block
      | continue
    predecessors := predecessors.modify index fun indices =>
      indices.push predecessorIndex
  predecessors

/-- Cache reachable predecessor indices once, outside the iterative solver. -/
@[expose] def collectPredecessors
    (reversePostOrder : Array BlockPtr)
    (blockIndex : HashMap BlockPtr Nat)
    (irCtx : WfIRContext OpCode) : Array (Array Nat) := Id.run do
  let mut predecessors := Array.replicate reversePostOrder.size #[]
  for h : predecessorIndex in [:reversePostOrder.size] do
    let predecessor := reversePostOrder[predecessorIndex]
    predecessors := addPredecessorEdges predecessors predecessorIndex
      (predecessor.getSuccessors! irCtx.raw) blockIndex
  predecessors

/-- Build the inverse map from reachable blocks to their dense RPO indices. -/
@[expose] def buildBlockIndex
    (reversePostOrder : Array BlockPtr) : HashMap BlockPtr Nat := Id.run do
  let mut blockIndex : HashMap BlockPtr Nat := {}
  for h : index in [:reversePostOrder.size] do
    blockIndex := blockIndex.insert reversePostOrder[index] index
  blockIndex

/-- Collect all fixed dominance metadata for a region. -/
@[expose] def collectMetadata
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode) : RegionDominanceMetadata :=
  let reversePostOrder := (collectPostOrder region irCtx).reverse
  let blockIndex := buildBlockIndex reversePostOrder
  let predecessors := collectPredecessors reversePostOrder blockIndex irCtx
  { reversePostOrder, blockIndex, predecessors }

/-- Build a temporary hash index of represented CFG edges for metadata validation. -/
@[expose] def collectEdges
    (metadata : RegionDominanceMetadata)
    (irCtx : WfIRContext OpCode) : HashSet (BlockPtr × BlockPtr) :=
  HashSet.ofList <| metadata.reversePostOrder.toList.flatMap fun predecessor =>
    (predecessor.getSuccessors! irCtx.raw).toList.map fun block => (predecessor, block)

/-- Check that one cached predecessor index denotes an actual CFG edge. -/
@[expose] def predecessorIndexIsValid
    (metadata : RegionDominanceMetadata)
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (edges : HashSet (BlockPtr × BlockPtr))
    (blockIndex predecessorIndex : Nat) : Bool :=
  match metadata.reversePostOrder[blockIndex]?,
      metadata.reversePostOrder[predecessorIndex]? with
  | some block, some predecessor =>
    decide ((predecessor.get! irCtx.raw).parent = some region) &&
      metadata.blockIndex.get? predecessor = some predecessorIndex &&
      edges.contains (predecessor, block)
  | _, _ => false

/--
Check the fixed structural metadata consumed by the CHK solver.

The check is deliberately independent of the mutable dominance value. Besides
certifying the cached predecessor edges, it establishes that the RPO array is
injective (through its inverse map) and that every non-entry block has an
earlier predecessor. The latter is the only ordering property required by the
semantic proof.
-/
@[expose] def metadataIsValid
    (metadata : RegionDominanceMetadata)
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode) : Bool :=
  match (region.get! irCtx.raw).firstBlock, metadata.reversePostOrder[0]? with
  | some entry, some firstBlock =>
    let edges := collectEdges metadata irCtx
    entry = firstBlock &&
      metadata.predecessors.size = metadata.reversePostOrder.size &&
      (List.range metadata.reversePostOrder.size).all fun blockIndex =>
        let block := metadata.reversePostOrder[blockIndex]!
        (block.get! irCtx.raw).parent = some region &&
          metadata.blockIndex.get? block = some blockIndex &&
          (metadata.predecessors[blockIndex]!.all fun predecessorIndex =>
            predecessorIndexIsValid metadata region irCtx edges
              blockIndex predecessorIndex) &&
          (blockIndex = 0 ||
            metadata.predecessors[blockIndex]!.any fun predecessorIndex =>
              predecessorIndex < blockIndex)
  | _, _ => false

/-- Collect metadata and retain it only when its solver contract is certified. -/
@[expose] def collectMetadata?
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode) : Option RegionDominanceMetadata :=
  let metadata := collectMetadata region irCtx
  if metadataIsValid metadata region irCtx then some metadata else none

/-- Initialize a region dominance fact and enqueue its first reverse postorder sweep. -/
private def initializeRegion
    (region : RegionPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  let some entry := (region.get! irCtx.raw).firstBlock
    | return dfCtx
  let some metadata := collectMetadata? region irCtx
    | return dfCtx
  let latticeElement := DominanceValue.initial metadata.reversePostOrder.size
  dfCtx :=
    dfCtx.modifyFactAndPropagate .regionDominance (.BlockPtr entry) (fun fact =>
      ({ fact with payload :=
          { metadata, latticeElement } }, true)) irCtx
  dfCtx.enqueue (InsertPoint.atStart! entry irCtx.raw, kind)

/-- Recursively initialize the analysis on nested regions. -/
partial def init
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx

  for region in op.getRegions! irCtx.raw do
    dfCtx := initializeRegion region dfCtx irCtx

    let mut currentBlock := (region.get! irCtx.raw).firstBlock
    while let some block := currentBlock do
      let mut currentOp := (block.get! irCtx.raw).firstOp
      while let some nestedOp := currentOp do
        dfCtx := init nestedOp dfCtx irCtx
        currentOp := (nestedOp.get! irCtx.raw).next
      currentBlock := (block.get! irCtx.raw).next

  dfCtx
/-- Incorporate one predecessor into the current CHK candidate and waiting flag. -/
@[expose]
def predecessorStep
    (latticeElement : DominanceValue blockCount)
    (state : Option Nat × Bool)
    (predecessorIndex : Nat) : Option Nat × Bool :=
  if latticeElement.get! predecessorIndex = blockCount then
    (state.1, true)
  else
    (some (match state.1 with
      | none => predecessorIndex
      | some immediateDominatorIndex =>
          latticeElement.intersect predecessorIndex immediateDominatorIndex), state.2)

/--
Compute the next immediate dominator candidate for `block`.

The entry block dominates itself. For every other block, we scan its predecessors,
pick the first one whose working immediate dominator has already been computed, and then
repeatedly `intersect` that candidate with each other processed predecessor.

The boolean result reports whether a reachable predecessor is still waiting for
its first immediate dominator value, in which case the region needs another sweep.
-/
@[expose]
def computeImmediateDominator
    (blockIndex : Nat)
    (predecessors : Array (Array Nat))
    (latticeElement : DominanceValue blockCount) : Option Nat × Bool :=
  if blockIndex = 0 then
    (some 0, false)
  else
    predecessors[blockIndex]!.foldl (predecessorStep latticeElement) (none, false)

/-- The mutable state produced by one complete CHK reverse-postorder sweep. -/
structure SweepResult (blockCount : Nat) where
  latticeElement : DominanceValue blockCount
  latticeElementChanged : Bool
  needsSweep : Bool

/-- Run one complete CHK reverse-postorder sweep over the dense region value. -/
@[expose] def sweep
    (predecessors : Array (Array Nat))
    (initialValue : DominanceValue blockCount) : SweepResult blockCount := Id.run do
  let mut latticeElement := initialValue
  let mut latticeElementChanged := false
  let mut needsSweep := false
  -- Index zero is the entry block, whose immediate dominator is fixed at zero.
  for blockIndex in [1:blockCount] do
    let (newIDomIndex?, waiting) :=
      computeImmediateDominator blockIndex predecessors latticeElement
    needsSweep := needsSweep || waiting
    if let some newIDomIndex := newIDomIndex? then
      let oldIDomIndex := latticeElement.get! blockIndex
      let refinedIDomIndex := min oldIDomIndex newIDomIndex
      -- Once initialized, a block is stable only when its stored parent is
      -- exactly the freshly computed CHK candidate.
      needsSweep := needsSweep ||
        (oldIDomIndex ≠ blockCount && oldIDomIndex ≠ newIDomIndex)
      if oldIDomIndex ≠ refinedIDomIndex then
        -- Initializing a fact cannot invalidate an earlier chain traversal: no
        -- traversal can pass through a block before that block has an iDom.
        -- A refinement of an existing fact can, so it requires another sweep.
        latticeElementChanged := true
        latticeElement := latticeElement.refine! blockIndex newIDomIndex
  return { latticeElement, latticeElementChanged, needsSweep }

/--
Perform one complete Cooper-Harvey-Kennedy reverse postorder sweep.

If an initialized immediate dominator changes, or a reachable predecessor is
still uninitialized, the region entry is re-enqueued for another sweep.
-/
def visit
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode) : DataFlowContext := Id.run do
  if point.prev! irCtx.raw ≠ none then
    return dfCtx
  let block := (point.block! irCtx.raw).get!
  let region := ((block.get! irCtx.raw).parent).get!
  let entry := ((region.get! irCtx.raw).firstBlock).get!
  let some dominance := region.getRegionDominanceFact? dfCtx irCtx
    | return dfCtx
  let mut dfCtx := dfCtx
  let sweepResult := sweep dominance.predecessors dominance.dominanceValue
  if sweepResult.latticeElementChanged then
    dfCtx := dfCtx.modifyFactAndPropagate .regionDominance (.BlockPtr entry) (fun fact =>
      (fact.setLatticeElement sweepResult.latticeElement, true)) irCtx
  if sweepResult.needsSweep then
    dfCtx := dfCtx.enqueue (InsertPoint.atStart! entry irCtx.raw, kind)
  dfCtx

end DominanceAnalysis

def DominanceAnalysis : DataFlowAnalysis :=
  { kind := DominanceAnalysis.kind
    init := DominanceAnalysis.init
    visit := DominanceAnalysis.visit }

end Veir
