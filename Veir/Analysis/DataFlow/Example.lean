module

public import Veir.Analysis.DataFlowFramework

public section

namespace Veir

class Join (α : Type) where
  join : α -> α -> α

class Meet (α : Type) where
  meet : α -> α -> α

structure ConstantValue where
  constant : Option Nat
deriving BEq

instance : Join ConstantValue where
  join (lhs rhs : ConstantValue) : ConstantValue :=
    if lhs.constant == rhs.constant then
      lhs
    else
      ⟨none⟩

-- ====================== Example `AnalysisState` Children ======================= --
structure AbstractSparseLatticeState extends BaseAnalysisState where
  useDefSubscribers : Array DataFlowAnalysis

instance : Update AbstractSparseLatticeState DataFlowContext where
  onUpdate (state : AbstractSparseLatticeState) (dfCtx : DataFlowContext)
      (irCtx : IRContext) : DataFlowContext := Id.run do
    let mut dfCtx := { dfCtx with workList := state.onUpdate dfCtx }
    match state.anchor with
    | .ValuePtr value =>
      let mut maybeUse := value.getFirstUse! irCtx
      while h : maybeUse.isSome do
        let use := maybeUse.get h
        let user := (use.get! irCtx).owner
        for analysis in state.useDefSubscribers do
          dfCtx := { dfCtx with workList := dfCtx.workList.enqueue (.OperationPtr user, analysis) }
        maybeUse := (use.get! irCtx).nextUse
    | _ =>
      pure ()
    dfCtx

structure ConstantLatticeState extends AbstractSparseLatticeState where
  value : ConstantValue
deriving TypeName

instance : Update ConstantLatticeState DataFlowContext where
  onUpdate state dfCtx irCtx :=
    Update.onUpdate
      state.toAbstractSparseLatticeState
      dfCtx
      irCtx

def ConstantLatticeState.new (value : ValuePtr) (constant : ConstantValue) : AnalysisState :=
  AnalysisState.new
    ({ anchor := .ValuePtr value
       dependents := #[]
       useDefSubscribers := #[]
       value := constant } : ConstantLatticeState)

-- =============================================================================== --

-- ===================== Example `DataFlowAnalysis` Children ===================== --
namespace ConstantAnalysis

abbrev OpCode.constant : Nat := 1
abbrev OpCode.addi : Nat := 2
abbrev OpCode.muli : Nat := 4
abbrev OpCode.andi : Nat := 5
abbrev OpCode.subi : Nat := 6

def unknownConstant : ConstantValue :=
  ⟨none⟩

def fromOperationProperty (op : OperationPtr) (irCtx : IRContext) : ConstantValue :=
  ⟨some (op.get! irCtx).properties.toNat⟩

def propagateConstant (value : ValuePtr) (constant : ConstantValue)
    (dfCtx : DataFlowContext) (irCtx : IRContext) : DataFlowContext := Id.run do
  let anchor : LatticeAnchor := .ValuePtr value
  match dfCtx.lattice[anchor]? with
  | none =>
    let state := ConstantLatticeState.new value constant
    let mut dfCtx := { dfCtx with lattice := dfCtx.lattice.insert anchor state }
    dfCtx := state.onUpdate dfCtx irCtx
    dfCtx
  | some existingState =>
    match existingState.getValue? ConstantLatticeState with
    | none =>
      -- Another analysis may already own this anchor in the simplified single-map
      -- lattice representation. Ignore instead of crashing.
      -- TODO: fix this! The lattice should be a map of maps based off the type
      dfCtx
    | some oldState =>
      let joined := Join.join oldState.value constant
      if joined == oldState.value then
        dfCtx
      else
        let nextState : ConstantLatticeState := { oldState with value := joined }
        let state := AnalysisState.new nextState
        let mut dfCtx := { dfCtx with lattice := dfCtx.lattice.insert anchor state }
        dfCtx := state.onUpdate dfCtx irCtx
        dfCtx

def setAllToUnknownConstants (values : Array ValuePtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  for value in values do
    dfCtx := propagateConstant value unknownConstant dfCtx irCtx
  dfCtx

def opResults (op : OperationPtr) (irCtx : IRContext) : Array ValuePtr := Id.run do
  let mut values : Array ValuePtr := #[]
  for i in [0:op.getNumResults! irCtx] do
    values := values.push (ValuePtr.opResult (op.getResult i))
  values

partial def blockArguments (block : BlockPtr) (irCtx : IRContext)
    (acc : Array ValuePtr := #[]) : Array ValuePtr := Id.run do
  let mut acc := acc
  for i in [0:block.getNumArguments! irCtx] do
    acc := acc.push (ValuePtr.blockArgument (block.getArgument i))
  match (block.get! irCtx).next with
  | some nextBlock =>
    blockArguments nextBlock irCtx acc
  | none =>
    acc

def regionArguments (region : RegionPtr) (irCtx : IRContext) : Array ValuePtr :=
  match (region.get! irCtx).firstBlock with
  | some firstBlock =>
    blockArguments firstBlock irCtx
  | none =>
    #[]

def setOpAndRegionValuesToUnknown (op : OperationPtr) (dfCtx : DataFlowContext)
    (irCtx : IRContext) : DataFlowContext := Id.run do
  let mut dfCtx := setAllToUnknownConstants (opResults op irCtx) dfCtx irCtx
  for i in [0:op.getNumRegions! irCtx] do
    let region := op.getRegion! irCtx i
    dfCtx := setAllToUnknownConstants (regionArguments region irCtx) dfCtx irCtx
  dfCtx

def getKnownConstant? (value : ValuePtr) (dfCtx : DataFlowContext) : Option Nat := do
  let anchor : LatticeAnchor := .ValuePtr value
  let state ← dfCtx.lattice[anchor]?
  let constantState ← state.getValue? ConstantLatticeState
  constantState.value.constant

def foldBinaryOp? (op : OperationPtr) (dfCtx : DataFlowContext) (irCtx : IRContext)
    (f : Nat → Nat → Option Nat) : Option ConstantValue :=
  if op.getNumResults! irCtx == 0 then
    none
  else if op.getNumOperands! irCtx != 2 then
    none
  else
    let lhsValue := op.getOperand! irCtx 0
    let rhsValue := op.getOperand! irCtx 1
    match getKnownConstant? lhsValue dfCtx, getKnownConstant? rhsValue dfCtx with
    | some lhs, some rhs =>
      match f lhs rhs with
      | some folded => some ⟨some folded⟩
      | none => none
    | _, _ => none

def foldSubiConstants? (lhs rhs : Nat) : Option Nat :=
  -- Without width/sign info, avoid unsound underflow behavior from Nat subtraction.
  if rhs ≤ lhs then
    some (lhs - rhs)
  else
    none

def visit (point : ProgramPoint) (dfCtx : DataFlowContext)
    (irCtx : IRContext) : DataFlowContext := Id.run do
  match point with
  | .OperationPtr op =>
    match (op.get! irCtx).opType with
    | OpCode.constant =>
      if op.getNumResults! irCtx > 0 then
        propagateConstant (ValuePtr.opResult (op.getResult 0)) (fromOperationProperty op irCtx) dfCtx irCtx
      else
        dfCtx
    | OpCode.addi =>
      match foldBinaryOp? op dfCtx irCtx (fun lhs rhs => some (lhs + rhs)) with
      | some constant =>
        propagateConstant (ValuePtr.opResult (op.getResult 0)) constant dfCtx irCtx
      | none =>
        setOpAndRegionValuesToUnknown op dfCtx irCtx
    | OpCode.muli =>
      match foldBinaryOp? op dfCtx irCtx (fun lhs rhs => some (lhs * rhs)) with
      | some constant =>
        propagateConstant (ValuePtr.opResult (op.getResult 0)) constant dfCtx irCtx
      | none =>
        setOpAndRegionValuesToUnknown op dfCtx irCtx
    | OpCode.andi =>
      match foldBinaryOp? op dfCtx irCtx (fun lhs rhs => some (Nat.land lhs rhs)) with
      | some constant =>
        propagateConstant (ValuePtr.opResult (op.getResult 0)) constant dfCtx irCtx
      | none =>
        setOpAndRegionValuesToUnknown op dfCtx irCtx
    | OpCode.subi =>
      match foldBinaryOp? op dfCtx irCtx foldSubiConstants? with
      | some constant =>
        propagateConstant (ValuePtr.opResult (op.getResult 0)) constant dfCtx irCtx
      | none =>
        setOpAndRegionValuesToUnknown op dfCtx irCtx
    | _ =>
      setOpAndRegionValuesToUnknown op dfCtx irCtx

-- Enqueue one operation after recursively enqueueing everything nested in its regions.
mutual
partial def enqueueOpPostOrder
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext) : DataFlowContext := Id.run do
  let mut dfCtx := dfCtx
  for i in [0:op.getNumRegions! irCtx] do
    let region := (op.getRegion! irCtx i).get! irCtx
    if h : region.firstBlock.isSome then
      let firstBlock := region.firstBlock.get h
      dfCtx := enqueueBlockList firstBlock dfCtx irCtx
  visit (.OperationPtr op) dfCtx irCtx

partial def enqueueOpList
    (op : OperationPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext) : DataFlowContext :=
  let dfCtx := enqueueOpPostOrder op dfCtx irCtx
  if h : (op.get! irCtx).next.isSome then
    let nextOp := (op.get! irCtx).next.get h
    enqueueOpList nextOp dfCtx irCtx
  else
    dfCtx

partial def enqueueBlockList
    (block : BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext) : DataFlowContext :=
  let dfCtx :=
    if h : (block.get! irCtx).firstOp.isSome then
      let firstOp := (block.get! irCtx).firstOp.get h
      enqueueOpList firstOp dfCtx irCtx
    else
      dfCtx
  if h : (block.get! irCtx).next.isSome then
    let nextBlock := (block.get! irCtx).next.get h
    enqueueBlockList nextBlock dfCtx irCtx
  else
    dfCtx

end

def init (top : OperationPtr) (dfCtx : DataFlowContext) (irCtx : IRContext) : DataFlowContext :=
  enqueueOpPostOrder top dfCtx irCtx

end ConstantAnalysis

def ConstantAnalysis :=
  DataFlowAnalysis.new
  ConstantAnalysis.init
  ConstantAnalysis.visit
-- =============================================================================== --

end Veir

