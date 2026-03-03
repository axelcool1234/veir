module

public import Veir.Analysis.DataFlowFramework

public section

namespace Veir

-- *=============================================================================*
-- |                          AnalysisState Children                             |
-- *=============================================================================*

-- ============================= SparseLatticeState ============================== --
structure SparseLatticeState (Domain : Type) extends AnalysisStateHeader where
  useDefSubscribers : Array Lean.Name
  latticeElement : Domain

@[reducible]
unsafe def instTypeNameSparseLatticeStateImpl [LatticeElement Domain] : TypeName (SparseLatticeState Domain) :=
  TypeName.mk _ ((TypeName.typeName Domain).appendBefore "SparseLatticeState_")

@[implemented_by instTypeNameSparseLatticeStateImpl]
opaque instTypeNameSparseLatticeState [LatticeElement Domain] : TypeName (SparseLatticeState Domain) := by
  classical
  exact Classical.choice inferInstance

attribute [instance] instTypeNameSparseLatticeState

instance [LatticeElement Domain] : AnalysisState (SparseLatticeState Domain) where
  typeNameInst := inferInstance
  mkState := fun anchor =>
    { anchor := anchor
      dependents := #[]
      useDefSubscribers := ∅
      latticeElement := LatticeElement.bottom }
  onUpdate (state : SparseLatticeState Domain) (dfCtx : DataFlowContext)
      (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
    let mut dfCtx := { dfCtx with workList := state.enqueueDependents dfCtx.workList }
    match state.anchor with
    | .ValuePtr ssaValue =>
      let mut maybeUse := ssaValue.getFirstUse! irCtx
      while h : maybeUse.isSome do
        let use := maybeUse.get h
        let user := (use.get! irCtx).owner
        for analysisId in state.useDefSubscribers do
          dfCtx := { dfCtx with workList := dfCtx.workList.enqueue (ProgramPoint.afterOp user irCtx, analysisId) }
        maybeUse := (use.get! irCtx).nextUse
    | _ =>
      pure ()
    dfCtx
  toHeader := SparseLatticeState.toAnalysisStateHeader

namespace SparseLatticeState

variable {Domain : Type}
variable [AnalysisState (SparseLatticeState Domain)] [LatticeElement Domain]

def useDefSubscribe (state : SparseLatticeState Domain)
    (analysisId : Lean.Name) : SparseLatticeState Domain :=
  if state.useDefSubscribers.contains analysisId then
    state
  else
    { state with useDefSubscribers := state.useDefSubscribers.push analysisId }

def getElement? (dfCtx : DataFlowContext) (ssaValue : ValuePtr) : Option Domain := do
  let state ← dfCtx.getState? (State := SparseLatticeState Domain) (.ValuePtr ssaValue)
  return state.latticeElement

def getElementD (dfCtx : DataFlowContext) (ssaValue : ValuePtr) (fallback : Domain) : Domain :=
  match getElement? (Domain := Domain) dfCtx ssaValue with
  | some latticeValue =>
    latticeValue
  | none =>
    fallback

end SparseLatticeState
-- =============================================================================== --

end Veir
