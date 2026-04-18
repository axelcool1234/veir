import Veir.Analysis.DataFlowFramework 
import Veir.Parser.MlirParser

import Veir.Analysis.DataFlow.DominanceAnalysis

open Std (HashMap)
open Veir
open Veir.Parser

namespace UnitTest.DataFlowFramework

abbrev MismatchReport := Array String

def renderReport (report : MismatchReport) : String :=
  if report.isEmpty then
    "ok"
  else
    "mismatches:\n" ++ String.intercalate "\n" report.toList

def parseTopLevelOp (s : String) : Except String (OperationPtr × MlirParserState) := do
  let some (ctx, _) := IRContext.create OpCode
    | throw "internal error: failed to create IR context"
  let parserState ← ParserState.fromInput (s.toByteArray)
  let (op, mlirState, _) ← (parseOp none).run (MlirParserState.fromContext ctx) parserState
  pure (op, mlirState)

def labeledBlockNames (mlir : String) : Array String := Id.run do
  let mut names := #[]
  for line in mlir.splitOn "\n" do
    let trimmed := (line.trimAsciiStart).toString
    if trimmed.startsWith "^" then
      let name := ((trimmed.drop 1).takeWhile fun c => c != ':' && c != '(').toString
      names := names.push name
  names

partial def collectBlocksDepthFirst
    (op : OperationPtr)
    (irCtx : IRContext OpCode)
    (acc : Array BlockPtr := #[]) : Array BlockPtr := Id.run do
  let mut acc := acc
  for i in [0:op.getNumRegions! irCtx] do
    let region := (op.getRegion! irCtx i).get! irCtx
    let mut maybeBlock := region.firstBlock
    while h : maybeBlock.isSome do
      let block := maybeBlock.get h
      acc := acc.push block
      let mut maybeOp := (block.get! irCtx).firstOp
      while hOp : maybeOp.isSome do
        let nestedOp := maybeOp.get hOp
        acc := collectBlocksDepthFirst nestedOp irCtx acc
        maybeOp := (nestedOp.get! irCtx).next
      maybeBlock := (block.get! irCtx).next
  acc

def namedBlocks?
    (top : OperationPtr)
    (irCtx : IRContext OpCode)
    (mlir : String) : Option (HashMap String BlockPtr) :=
  let names := labeledBlockNames mlir
  let blocks := collectBlocksDepthFirst top irCtx
  if names.size != blocks.size then
    none
  else
    some <| Id.run do
      let mut blockMap : HashMap String BlockPtr := HashMap.emptyWithCapacity names.size
      for i in [0:names.size] do
        blockMap := blockMap.insert names[i]! blocks[i]!
      blockMap

def runWithAnalyses
    (mlir : String)
    (analyses : Array DataFlowAnalysis)
    (check : OperationPtr -> DataFlowContext -> MlirParserState -> MismatchReport) : String :=
  match parseTopLevelOp mlir with
  | .error err =>
    s!"parse failed: {err}"
  | .ok (top, parserState) =>
    let dfCtx := fixpointSolve top analyses parserState.ctx
    renderReport (check top dfCtx parserState)

def compareNamedDominators
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode)
    (blockMap : HashMap String BlockPtr)
    (expected : Array (String × Option (Array String))) : MismatchReport := Id.run do
  let mut report := #[]
  for (name, expectedDoms?) in expected do
    match blockMap[name]? with
    | none =>
      report := report.push s!"dominators {name}: missing block label"
    | some block =>
      let observedReachable := (Veir.DominatorState.get? block dfCtx irCtx).isSome
      match expectedDoms? with
      | none =>
        if observedReachable then
          report := report.push s!"dominators {name}: expected unreachable block, observed initialized state"
      | some expectedDoms =>
        if !observedReachable then
          report := report.push s!"dominators {name}: expected initialized state, observed none"
        else
          for expectedDom in expectedDoms do
            match blockMap[expectedDom]? with
            | some expectedBlock =>
              if !Veir.DominanceAnalysis.dominates expectedBlock block dfCtx irCtx then
                report := report.push s!"dominators {name}: missing expected dominator {expectedDom}"
            | none =>
              report := report.push s!"dominators {name}: missing block label {expectedDom}"
          for (observedName, observedBlock) in blockMap.toList do
            if Veir.DominanceAnalysis.dominates observedBlock block dfCtx irCtx
                && !expectedDoms.contains observedName then
              report := report.push s!"dominators {name}: unexpected dominator {observedName}"
  report

namespace DominanceAnalysis

def run
    (mlir : String)
    (expected : Array (String × Option (Array String))) : String :=
  runWithAnalyses mlir #[Veir.DominanceAnalysis] (fun top dfCtx parserState => Id.run do
    let some blockMap := namedBlocks? top parserState.ctx mlir
      | return #["failed to recover named blocks from MLIR"]
    compareNamedDominators dfCtx parserState.ctx blockMap expected)

/-
  Test: loop with a backedge
            ┌───┐
            │ 0 │
            └─┬─┘
              │
              │
            ┌─▼─┐
            │ 1 ◄──┐
            └─┬─┘  │
              │    │
              │    │
            ┌─▼─┐  │
            │ 2 ├──┘
            └───┘
-/
def testDomLoop : String :=
  run
    "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1] : () -> ()\n\
^bb1:\n\
  \"test.test\"() [^bb2] : () -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb1] : () -> ()\n\
}) : () -> ()"
    #[ ("bb0", some #["bb0"])
     , ("bb1", some #["bb0", "bb1"])
     , ("bb2", some #["bb0", "bb1", "bb2"])
     ]

/-
  Test: diamond
         ┌───┐
      ┌──┤ 0 ├──┐
      │  └───┘  │
    ┌─▼─┐     ┌─▼─┐
    │ 1 │     │ 2 │
    └─┬─┘     └─┬─┘
      │  ┌───┐  │
      └──► 3 ◄──┘
         └───┘
-/
def testDomDiamond : String :=
  run
    "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1, ^bb2] : () -> ()\n\
^bb1:\n\
  \"test.test\"() [^bb3] : () -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb3] : () -> ()\n\
^bb3:\n\
  \"test.test\"() : () -> ()\n\
}) : () -> ()"
    #[ ("bb0", some #["bb0"])
     , ("bb1", some #["bb0", "bb1"])
     , ("bb2", some #["bb0", "bb2"])
     , ("bb3", some #["bb0", "bb3"])
     ]

/-
  Test: straight line
        ┌───┐
        │ 0 │
        └─┬─┘
          │
        ┌─▼─┐
        │ 1 │
        └─┬─┘
          │
        ┌─▼─┐
        │ 2 │
        └─┬─┘
          │
        ┌─▼─┐
        │ 3 │
        └───┘
-/
def testDomLine : String :=
  run
    "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1] : () -> ()\n\
^bb1:\n\
  \"test.test\"() [^bb2] : () -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb3] : () -> ()\n\
^bb3:\n\
  \"test.test\"() : () -> ()\n\
}) : () -> ()"
    #[ ("bb0", some #["bb0"])
     , ("bb1", some #["bb0", "bb1"])
     , ("bb2", some #["bb0", "bb1", "bb2"])
     , ("bb3", some #["bb0", "bb1", "bb2", "bb3"])
     ]


/-
  Test: entry branches to a while-loop or to an if-statement, then join.
                      ┌───┐
                  ┌───┤ 0 ├───┐
                  │   └───┘   │
                ┌─▼─┐       ┌─▼─┐
              ┌─► 1 │    ┌──┤ 2 ├──┐
              │ └─┬─┘    │  └───┘  │
              │   │    ┌─▼─┐     ┌─▼─┐
              │ ┌─▼─┐  │ 3 │     │ 4 │
              └─┤ 5 │  └─┬─┘     └─┬─┘
                └─┬─┘    │  ┌───┐  │
                  │      └──► 6 ◄──┘  
                  │         └─┬─┘
                  │   ┌───┐   │
                  └───► 7 ◄───┘
                      └───┘
-/
def testDomIfLoopIf : String :=
  run
    "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1, ^bb2] : () -> ()\n\
^bb1:\n\
  \"test.test\"() [^bb5] : () -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb3, ^bb4] : () -> ()\n\
^bb3:\n\
  \"test.test\"() [^bb6] : () -> ()\n\
^bb4:\n\
  \"test.test\"() [^bb6] : () -> ()\n\
^bb5:\n\
  \"test.test\"() [^bb1, ^bb7] : () -> ()\n\
^bb6:\n\
  \"test.test\"() [^bb7] : () -> ()\n\
^bb7:\n\
  \"test.test\"() : () -> ()\n\
}) : () -> ()"
    #[ ("bb0", some #["bb0"])
     , ("bb1", some #["bb0", "bb1"])
     , ("bb2", some #["bb0", "bb2"])
     , ("bb3", some #["bb0", "bb2", "bb3"])
     , ("bb4", some #["bb0", "bb2", "bb4"])
     , ("bb5", some #["bb0", "bb1", "bb5"])
     , ("bb6", some #["bb0", "bb2", "bb6"])
     , ("bb7", some #["bb0", "bb7"])
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomLoop

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomDiamond

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomLine

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomIfLoopIf

end DominanceAnalysis

