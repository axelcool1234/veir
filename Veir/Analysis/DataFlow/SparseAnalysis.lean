module

public import Veir.Analysis.DataFlow.SparseFact
public import Veir.Analysis.DataFlow.DeadCodeAnalysis

public section

namespace Veir

/--
The full specification of a sparse forward analysis, declared once per analysis.

It ties together the three things a sparse analysis would otherwise have to
register in separate places:
* the fact slot `kind` and its lattice `Domain` (inherited from `SparseFactSpec`), and
* the `AnalysisKind` tag the analysis is scheduled under.

Because the fact kind and the analysis kind live in the same instance, a custom
analysis can no longer desync them (e.g. by passing the wrong `AnalysisKind` to
`new`): `SparseForwardDataFlowAnalysis.new` reads the tag straight off this
instance, so the `(FactKind, AnalysisKind, Domain)` triple has a single source
of truth.
-/
class SparseForwardSpec (kind : FactKind) (Domain : outParam Type)
    extends SparseFactSpec kind Domain where
  /-- The `AnalysisKind` tag this sparse analysis is scheduled under. -/
  analysisKind : AnalysisKind

namespace SparseForwardDataFlowAnalysis

variable {kind : FactKind} {Domain : Type}

-- TODO: When this is verified, we will need something stronger than this for `Domain`
variable [Top Domain] [Bot Domain] [Join Domain] [DecidableEq Domain]

/--
The transfer function a custom sparse analysis supplies.

This is a *pure, domain-level* function: given an operation and the abstract
values of its operands (already read out of the lattice by the framework, in
operand order), it returns the abstract value of each result, in result order.

A custom analysis never touches `DataFlowContext`: the framework owns reading
operand states, deciding when operands are ready, subscribing for revisits, and
joining/propagating the results this function returns. That keeps the analysis
author's code in the same abstract-domain vocabulary their soundness proof lives
in (see `OpTransfer.Sound`).

When the array returned is shorter than the operation's result count, missing
results are conservatively treated as `⊤`.
-/
abbrev OpTransfer (Domain : Type) :=
  OperationPtr → IRContext OpCode → Array Domain → Array Domain

/--
The soundness contract for a sparse transfer, relative to a concrete operation
semantics `eval` (mapping an operation and concrete operand values to its
concrete result values).

`transfer` is sound when, for every operation, if each operand abstraction
over-approximates the corresponding concrete operand (`concrete ∈ γ abstract`),
then each result abstraction `transfer` produces over-approximates the
corresponding concrete result `eval` produces.

This is the single proof obligation a *verified* sparse analysis discharges. It
is stated entirely in `Domain`/`γ` terms — no `DataFlowContext`, no worklist — so
it composes directly with the abstract-domain lemmas an analysis already proves
(e.g. those for `ConstantDomain`). The generic driver is responsible, once and
for all, for turning a transfer satisfying this contract into a sound fixpoint;
the contract is the clean seam between the two.

Result/operand positions that are out of range are quantified vacuously via
`getElem?`, so this also captures the driver's "missing result ⇒ `⊤`" behavior
being conservative.
-/
def OpTransfer.Sound
    {Domain Concrete : Type} [LE Domain] [AbstractDomain Domain Concrete]
    (eval : OperationPtr → Array Concrete → IRContext OpCode → Array Concrete)
    (transfer : OpTransfer Domain) : Prop :=
  ∀ (op : OperationPtr) (irCtx : IRContext OpCode)
    (operandAbstractions : Array Domain) (operandConcretes : Array Concrete),
    (∀ (i : Nat) (a : Domain) (c : Concrete),
      operandAbstractions[i]? = some a → operandConcretes[i]? = some c →
      AbstractDomain.γ a c) →
    ∀ (i : Nat) (ra : Domain) (rc : Concrete),
      (transfer op irCtx operandAbstractions)[i]? = some ra →
      (eval op operandConcretes irCtx)[i]? = some rc →
      AbstractDomain.γ ra rc

/--
The maximally-imprecise transfer — every result `⊤` — is sound against *any*
concrete semantics.

This is the base case `γ_top` discharges, and a check that `OpTransfer.Sound` is
a genuinely dischargeable obligation rather than a vacuous one: a real analysis'
soundness proof bottoms out here on the operations it declines to interpret (in
`SparseConstantPropagation.transfer`, the region-op and `_` fallbacks, which both
return all `⊤`).
-/
theorem OpTransfer.sound_top
    {Domain Concrete : Type} [LE Domain] [AbstractDomain Domain Concrete]
    (eval : OperationPtr → Array Concrete → IRContext OpCode → Array Concrete) :
    OpTransfer.Sound eval
      (fun op irCtx _ => Array.replicate (op.getNumResults! irCtx) (⊤ : Domain)) := by
  intro op irCtx operandAbstractions operandConcretes _ i ra rc hra _
  simp only [Array.getElem?_replicate] at hra
  split at hra
  · have hra : ra = (⊤ : Domain) := by simpa using hra.symm
    subst hra
    rw [AbstractDomain.γ_top]
    trivial
  · simp at hra

/--
Join a sparse lattice fact into the target value state and propagate updates
when it changes.

This is the generic sparse analysis primitive that merges an incoming lattice
element into the stored state for an SSA value.
-/
@[expose] def joinLatticeElement
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    (target : ValuePtr)
    (incoming : Domain)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let oldValue := SparseFact.getElementD kind target ⊥ dfCtx
  let newValue := oldValue ⊔ incoming
  if newValue = oldValue then
    return dfCtx
  dfCtx.modifyFactAndPropagate kind (.ValuePtr target) 
    (SparseFact.setLatticeElement · newValue, true) irCtx

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
Return the SSA value forwarded to the given successor's block argument, if any.
-/
private def getSuccessorOperand?
    (op : OperationPtr)
    (successorIndex : Nat)
    (argumentIndex : Nat)
    (irCtx : IRContext OpCode) : Option ValuePtr :=
  if successorIndex >= op.getNumSuccessors! irCtx then
    panic! s!"SparseForwardDataFlowAnalysis.getSuccessorOperand?: successor index {successorIndex} out of range"
  else
    match (op.get! irCtx).opType with
    -- TODO: Replace this `.test .test` check once VeIR has proper branch ops.
    -- `successorIndex` will become relevant then.
    | .test .test =>
      if argumentIndex < op.getNumOperands! irCtx then
        some (op.getOperand! irCtx argumentIndex)
      else
        none
    | _ =>
      panic! "SparseForwardDataFlowAnalysis.getSuccessorOperand?: non-branch op"

/--
Conservatively treat blocks as executable when dead code analysis is
not registered. Otherwise consult the executable lattice, where points
are not live by default.
-/
private def isBlockExecutable
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : Bool :=
  if !dfCtx.hasAnalysis .deadCode then
    true
  else
    let blockPoint := InsertPoint.atStart! block irCtx
    match dfCtx.getFact? .executable (.InsertPoint blockPoint) with
    | some executableFact => executableFact.live
    | none => false

/--
Conservatively treat CFG edges as executable when dead code analysis is
not registered. Otherwise consult the executable lattice, where points are
not live by default.
-/
private def isEdgeExecutable
    (edge : CFGEdge)
    (dfCtx : DataFlowContext)
    (_irCtx : IRContext OpCode) : Bool :=
  if !dfCtx.hasAnalysis .deadCode then
    true
  else
    match dfCtx.getFact? .executable (.CFGEdge edge) with
    | some executableFact => executableFact.live
    | none => false

/-- Subscribe to block executability updates if dead code analysis is registered. -/
private def subscribeToBlockExecutability
    (analysisKind : AnalysisKind)
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  if !dfCtx.hasAnalysis .deadCode then
    dfCtx
  else
    let blockPoint := InsertPoint.atStart! block irCtx
    dfCtx.modifyFact .executable (.InsertPoint blockPoint) (fun state =>
      state.subscribe analysisKind)

/-- Subscribe to edge executability updates if dead code analysis is registered. -/
private def subscribeToEdgeExecutability
    (analysisKind : AnalysisKind)
    (edge : CFGEdge)
    (dfCtx : DataFlowContext) : DataFlowContext :=
  if !dfCtx.hasAnalysis .deadCode then
    dfCtx
  else
    dfCtx.modifyFact .executable (.CFGEdge edge) (fun state =>
      state.subscribe analysisKind)

/--
Visit a block during sparse initialization.
-/
private def visitBlock
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    (analysisKind : AnalysisKind)
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- Exit early on blocks with no arguments.
  if block.getNumArguments! irCtx = 0 then
    return dfCtx 

  -- If the block is not executable, bail out.
  if !isBlockExecutable block dfCtx irCtx then
    return dfCtx

  let some parentRegion := (block.get! irCtx).parent
    | return dfCtx

  -- The argument lattices of entry blocks are set by region control flow or
  -- the callgraph.
  if (parentRegion.get! irCtx).firstBlock = some block then
    -- TODO: Mirror MLIR's handling of `visitCallableOperation` and
    -- `visitRegionSuccessors` and `visitNonControlFlowArgumentsImpl`
    -- for entry blocks.
    return dfCtx

  let mut dfCtx := dfCtx

  -- Iterate over the predecessors of the non-entry block.
  let mut maybePredUse := (block.get! irCtx).firstUse

  while let some predUse := maybePredUse do
    let predUseStruct := predUse.get! irCtx
    maybePredUse := predUseStruct.nextUse

    let predecessorOp := predUseStruct.owner
    let some predecessorBlock := (predecessorOp.get! irCtx).parent
      | continue

    let edge : CFGEdge := { source := predecessorBlock, target := block }
    dfCtx := subscribeToEdgeExecutability analysisKind edge dfCtx

    -- If the edge from the predecessor block to the current block is not live,
    -- bail out.
    if !isEdgeExecutable edge dfCtx irCtx then
      continue

    -- Check if we can reason about the dataflow from the predecessor.
    if !isBranchOp predecessorOp irCtx then
      for target in block.getArguments! irCtx do
        dfCtx := joinLatticeElement kind target ⊤ dfCtx irCtx
      return dfCtx

    for i in [0:block.getNumArguments! irCtx] do
      let arg := block.getArgument i
      match getSuccessorOperand? predecessorOp predUse.index i irCtx with
      | some operand =>
        -- Add the current block start program point as a dependency of the
        -- predecessor block's successor operand lattice state, so this block
        -- is revisited when that operand lattice changes.
        let dependentPoint := InsertPoint.atStart! block irCtx
        let workItem : WorkItem := (dependentPoint, analysisKind)
        dfCtx := dfCtx.modifyFact kind (.ValuePtr operand) (fun state =>
          if state.dependents.any (fun dependent =>
              dependent.1 = dependentPoint && dependent.2 = analysisKind) then
            -- Do not add dependent again if it's already added.
            state
          else
            state.addDependent workItem)

        -- Call transfer function
        let incoming :=
          SparseFact.getElementD kind operand ⊥ dfCtx
        dfCtx := joinLatticeElement kind arg incoming dfCtx irCtx
      | none =>
        -- Conservatively consider internally produced arguments to be at the
        -- pessimistic sparse state.
        dfCtx := joinLatticeElement kind arg ⊤ dfCtx irCtx

  return dfCtx

mutual

/--
Ensure an operand has a sparse lattice state and subscribe the current sparse
analysis to its updates. This is what makes use-def driven revisitation work.
-/
partial def subscribeToOperand
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    (analysisKind : AnalysisKind)
    (operand : ValuePtr)
    (dfCtx : DataFlowContext) : DataFlowContext :=
  dfCtx.modifyFact kind (.ValuePtr operand) (fun state =>
    state.subscribe analysisKind)

/--
Visit one operation in the sparse analysis.

The framework owns all of the `DataFlowContext` plumbing here: it subscribes to
the operand lattices (so the operation is revisited when they change), reads the
operands' current abstractions, waits until they are all initialized, runs the
analysis' pure `transfer`, and joins each returned result abstraction back into
the lattice (propagating on change). The analysis itself only sees `Domain`s.
-/
partial def visitOperation
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    (analysisKind : AnalysisKind)
    (transfer : OpTransfer Domain)
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- Exit early on operations with no results.
  if op.getNumResults! irCtx = 0 then
    return dfCtx

  -- If the containing block is not executable, bail out. Executability is
  -- unreachable until proven live, so a missing state is treated as dead.
  if let some parentBlock := (op.get! irCtx).parent then
    if !isBlockExecutable parentBlock dfCtx irCtx then
      return dfCtx

  -- TODO: Mirror MLIR more closely by `visitRegionSuccessors`
  -- Comment: The results of a region branch operation are determined by control-flow.

  -- TODO: Mirror MLIR more closely by `visitCallOperation`

  let mut dfCtx := dfCtx
  for operand in op.getOperands! irCtx do
    dfCtx := subscribeToOperand kind analysisKind operand dfCtx

  -- Read the operands' current abstractions (⊥ = not yet computed).
  let operandAbstractions := (op.getOperands! irCtx).map
    (SparseFact.getElementD kind · ⊥ dfCtx)

  -- Optimistically wait until every operand has a value before transferring.
  if operandAbstractions.any (fun abstraction => abstraction = ⊥) then
    return dfCtx

  -- Run the analysis' pure transfer function and join each result abstraction.
  let resultAbstractions := transfer op irCtx operandAbstractions
  let mut resultIndex := 0
  for result in op.getResults! irCtx do
    let incoming := (resultAbstractions[resultIndex]?).getD ⊤
    dfCtx := joinLatticeElement kind result incoming dfCtx irCtx
    resultIndex := resultIndex + 1
  return dfCtx

/--
Recursively initialize an operation tree for sparse analysis.
Visit the current operation first, then walk its nested regions, 
blocks, and nested operations.
-/
partial def initializeRecursively
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    (analysisKind : AnalysisKind)
    (transfer : OpTransfer Domain)
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- Initialize the analysis by visiting every owner of an SSA value (all
  -- operations and blocks).
  let mut dfCtx := dfCtx
  dfCtx := visitOperation kind analysisKind transfer op dfCtx irCtx

  for regionPtr in (op.get! irCtx).regions do
    let region := regionPtr.get! irCtx
    let mut maybeBlock := region.firstBlock

    while let some block := maybeBlock do
      dfCtx := subscribeToBlockExecutability analysisKind block dfCtx irCtx
      dfCtx := visitBlock kind analysisKind block dfCtx irCtx
      let mut maybeOp := (block.get! irCtx).firstOp

      while let some nestedOp := maybeOp do
        dfCtx := initializeRecursively kind analysisKind transfer nestedOp dfCtx irCtx
        maybeOp := (nestedOp.get! irCtx).next

      maybeBlock := (block.get! irCtx).next
  dfCtx

end

/--
Initialize the analysis by visiting every owner of an SSA value: all
operations and blocks.
-/
private def init
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    (analysisKind : AnalysisKind)
    (transfer : OpTransfer Domain)
    (top : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  -- Mark the entry block arguments as having reached their pessimistic
  -- fixpoints.
  let mut dfCtx := dfCtx
  for regionPtr in (top.get! irCtx).regions do
    let region := regionPtr.get! irCtx
    if let some firstBlock := region.firstBlock then
      for arg in firstBlock.getArguments! irCtx do
        dfCtx := joinLatticeElement kind arg ⊤ dfCtx irCtx

  initializeRecursively kind analysisKind transfer top dfCtx irCtx

/--
Visit an insertion point. If this is at beginning of block and all
control flow predecessors or callsites are known, then the arguments
lattices are propagated from them. If this is after call operation or an
operation with region control-flow, then its result lattices are set
accordingly. Otherwise, the operation transfer function is invoked.
-/
private def visit
    (kind : FactKind)
    [SparseFactSpec kind Domain]
    (analysisKind : AnalysisKind)
    (transfer : OpTransfer Domain)
    (point : InsertPoint)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : DataFlowContext :=
  match point.prev! irCtx with
  | some prevOp =>
    visitOperation kind analysisKind transfer prevOp dfCtx irCtx
  | none =>
    match point.block! irCtx with
    | some block =>
      visitBlock kind analysisKind block dfCtx irCtx
    | none =>
      dfCtx

/--
Build a sparse forward analysis over one abstract value domain.

The fact slot `kind`, its lattice `Domain`, and the `AnalysisKind` tag all come
from the single `SparseForwardSpec` instance, so the only thing a custom
analysis supplies here is its transfer function.

Sparse facts default to `⊥`. Whenever control flow or transfer functions lose
precision, the framework conservatively joins `⊤` into the affected values.
-/
def new
    (kind : FactKind)
    [spec : SparseForwardSpec kind Domain]
    (transfer : OpTransfer Domain)
    : DataFlowAnalysis :=
  let analysisKind := spec.analysisKind
  { kind := analysisKind
    init := init kind analysisKind transfer
    visit := visit kind analysisKind transfer }

end SparseForwardDataFlowAnalysis

end Veir
