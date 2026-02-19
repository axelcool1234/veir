module

public import Std.Data.HashMap
public import Std.Data.HashSet
public import Init.Data.Queue
public import Veir.IR.Basic

open Std(HashSet)
open Std(HashMap)
open Std(Queue)

public section

namespace Veir

inductive ProgramPoint where
  | OperationPtr

inductive LatticeAnchor
  | ProgramPoint
  | ValuePtr 
deriving BEq, Hashable

-- =============================== DataFlowAnalysis ============================== -- 
-- NEVER use this type directly, use `DataFlowAnalysis` which provides a proof that
-- `dfCtx` is always of type `DataFlowContext`
structure RawDataFlowAnalysis where 
  dfCtx : Type u -- Always `DataFlowContext`
  init : OperationPtr -> dfCtx -> IRContext -> dfCtx
  visit : ProgramPoint -> dfCtx -> IRContext -> dfCtx

structure DataFlowAnalysisPtr where
  id: Nat

instance : Coe DataFlowAnalysisPtr Nat where
  coe ptr := ptr.id
-- =============================================================================== -- 

-- ================================== WorkList =================================== -- 
-- A queued item stores a program point and the index of the analysis to run.
@[expose] def WorkItem := ProgramPoint × DataFlowAnalysisPtr
@[expose] def WorkList := Queue WorkItem
-- =============================================================================== -- 

-- ================================ AnalysisState ================================ -- 
-- Lattice Elements are stored in structures that implement the `Update` typeclass.
-- These structures extend `BaseAnalysisState` along storing with anything else it needs.
-- `AnalysisState` is used to allow for dynamic dispatch (runtime polymorphism).
class Update (State : Type u) (Ctx : Type v) where
  onUpdate : State -> Ctx -> Ctx

structure BaseAnalysisState where
  anchor : LatticeAnchor
  dependents : Array WorkItem 

def BaseAnalysisState.onUpdate (state : BaseAnalysisState) (workList : WorkList) : WorkList := Id.run do
  let mut workList := workList 
  for workItem in state.dependents do
    workList := workList.enqueue workItem
  workList  

-- NEVER use this type directly, use `AnalysisState` which provides a proof that
-- `dfCtx` is always of type `DataFlowContext`
structure RawAnalysisState where -- record-of-functions style
  impl : Type u -- struct that extends `BaseAnalysisState` and contains some extra data
  dfCtx : Type v -- Always `DataFlowContext`
  value : impl
  onUpdate : Update impl dfCtx

-- =============================================================================== -- 

-- =============================== DataFlowContext =============================== -- 
structure DataFlowContext where 
  lattice : HashMap LatticeAnchor RawAnalysisState
  workList : WorkList

def DataFlowContext.empty : DataFlowContext :=
  { lattice := ∅
    workList := .empty
  }

instance : Coe DataFlowContext WorkList where
  coe dfCtx := dfCtx.workList

-- =============================================================================== -- 

-- ========================== DataFlowContext Wrappers =========================== -- 
-- Wrapper proving that a `RawDataFlowAnalysis` is specialized to `DataFlowContext`.
structure DataFlowAnalysis where
  val : RawDataFlowAnalysis
  hdfCtx : val.dfCtx = DataFlowContext

namespace DataFlowAnalysis

def init (analysis : DataFlowAnalysis) (top : OperationPtr) (dfCtx : DataFlowContext) (irCtx : IRContext) : DataFlowContext := by
  cases analysis with
  | mk val hdfCtx =>
    cases val with
    | mk _ init _ =>
      cases hdfCtx
      exact init top dfCtx irCtx

def visit (analysis : DataFlowAnalysis) (point : ProgramPoint) (dfCtx : DataFlowContext) (irCtx : IRContext) : DataFlowContext := by
  cases analysis with
  | mk val hdfCtx =>
    cases val with
    | mk _ _ visit =>
      cases hdfCtx
      exact visit point dfCtx irCtx

def toRaw (analysis : DataFlowAnalysis) : RawDataFlowAnalysis :=
  analysis.val

def new
    (init : OperationPtr -> DataFlowContext -> IRContext -> DataFlowContext)
    (visit : ProgramPoint -> DataFlowContext -> IRContext -> DataFlowContext) : DataFlowAnalysis :=
  { val := { dfCtx := DataFlowContext 
             init := init
             visit := visit }
    hdfCtx := rfl
  }

end DataFlowAnalysis

-- Wrapper proving that a `RawAnalysisState` is specialized to `DataFlowContext`.
structure AnalysisState where
  val : RawAnalysisState
  hdfCtx : val.dfCtx = DataFlowContext

namespace AnalysisState

def onUpdate (state : AnalysisState) (dfCtx : DataFlowContext) : DataFlowContext := by
  cases state with
  | mk val hdfCtx =>
    cases val with
    | mk Impl _ value onUpdate =>
      cases hdfCtx
      letI : Update Impl DataFlowContext := onUpdate
      exact Update.onUpdate value dfCtx

def toRaw (state : AnalysisState) : RawAnalysisState :=
  state.val

def new (value : Impl) [Update Impl DataFlowContext] : AnalysisState :=
  { val := { impl := Impl
             dfCtx := DataFlowContext
             value := value
             onUpdate := inferInstance }
    hdfCtx := rfl
  }

end AnalysisState
-- =============================================================================== -- 

-- =============================== Fixpoint Solver =============================== -- 
partial def run (analyses : Array DataFlowAnalysis) (dfCtx : DataFlowContext) (irCtx : IRContext) : DataFlowContext :=
  match dfCtx.workList.dequeue? with
  | none =>
    dfCtx
  | some ((point, dataFlowAnalysisPtr), workList) =>
    let dfCtx := { dfCtx with workList := workList }
    let dfCtx :=
      if h : dataFlowAnalysisPtr < analyses.size then
        let analysis := analyses[dataFlowAnalysisPtr.id]'h
        analysis.visit point dfCtx irCtx
      else
        dbg_trace "Invalid DataFlowAnalysisPtr!"
        dfCtx
    run analyses dfCtx irCtx

def fixpointSolve (top: OperationPtr) (analyses : Array DataFlowAnalysis) (irCtx : IRContext) : DataFlowContext := Id.run do
  -- init
  let mut dfCtx := DataFlowContext.empty
  for analysis in analyses do
    dfCtx := analysis.init top dfCtx irCtx

  -- run
  run analyses dfCtx irCtx

-- =============================================================================== -- 

end Veir
