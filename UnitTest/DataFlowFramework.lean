import Veir.Analysis.DataFlowFramework
import Veir.Analysis.DataFlow.Example
import Veir.Parser.MlirParser

open Std (HashMap)
open Veir
open Veir.Parser

macro "#assert! " e:term : command =>
  `(command| /--
    info: true
  -/
  #guard_msgs in
  #eval! $e)

def parseTopLevelOp (s : String) : Option (OperationPtr × MlirParserState) :=
  match IRContext.create with
  | none =>
    none
  | some (ctx, _) =>
    match ParserState.fromInput (s.toByteArray) with
    | .error err =>
      dbg_trace err
      none
    | .ok parserState =>
      match (parseOp none).run (MlirParserState.fromContext ctx) parserState with
      | .error err =>
        dbg_trace err
        none
      | .ok (op, mlirState, _) =>
        some (op, mlirState)

def lookupConstantValue?
    (dfCtx : DataFlowContext)
    (anchor : LatticeAnchor) : Option ConstantValue := do
  let state ← dfCtx.lattice[anchor]?
  let constState ← state.getValue? ConstantLatticeState
  return constState.value

def checkExpectedLattice
    (dfCtx : DataFlowContext)
    (valueDefs : HashMap ByteArray ValuePtr)
    (expected : Array (String × ConstantValue)) : Bool := Id.run do
  if dfCtx.lattice.size != expected.size then
    return false

  for (name, expectedValue) in expected do
    let some value := valueDefs[name.toByteArray]? | return false
    let anchor : LatticeAnchor := .ValuePtr value
    let some observedValue := lookupConstantValue? dfCtx anchor | return false
    if observedValue != expectedValue then
      return false

  true

abbrev ConstantValuePropagationAnalysis : DataFlowAnalysis :=
  ConstantAnalysis

def runConstantValuePropagation
    (mlir : String)
    (expected : Array (String × ConstantValue)) : Bool :=
  match parseTopLevelOp mlir with
  | none =>
    false
  | some (top, parserState) =>
    let dfCtx := fixpointSolve top #[ConstantValuePropagationAnalysis] parserState.ctx
    checkExpectedLattice dfCtx parserState.values expected

def testAddiAllConstant : Bool :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() : () -> i32\n\
  %b = \"arith.constant\"() : () -> i32\n\
  %c = \"arith.addi\"(%a, %b) : (i32, i32) -> i32\n\
}) : () -> ()"
  runConstantValuePropagation mlir
    #[ ("a", ⟨some 0⟩)
     , ("b", ⟨some 0⟩)
     , ("c", ⟨some 0⟩)
     ]

def testMuliAllConstant : Bool :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() : () -> i32\n\
  %b = \"arith.constant\"() : () -> i32\n\
  %c = \"arith.muli\"(%a, %b) : (i32, i32) -> i32\n\
}) : () -> ()"
  runConstantValuePropagation mlir
    #[ ("a", ⟨some 0⟩)
     , ("b", ⟨some 0⟩)
     , ("c", ⟨some 0⟩)
     ]

def testAndiAllConstant : Bool :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() : () -> i32\n\
  %b = \"arith.constant\"() : () -> i32\n\
  %c = \"arith.andi\"(%a, %b) : (i32, i32) -> i32\n\
}) : () -> ()"
  runConstantValuePropagation mlir
    #[ ("a", ⟨some 0⟩)
     , ("b", ⟨some 0⟩)
     , ("c", ⟨some 0⟩)
     ]

def testSubiAllConstant : Bool :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() : () -> i32\n\
  %b = \"arith.constant\"() : () -> i32\n\
  %c = \"arith.subi\"(%a, %b) : (i32, i32) -> i32\n\
}) : () -> ()"
  runConstantValuePropagation mlir
    #[ ("a", ⟨some 0⟩)
     , ("b", ⟨some 0⟩)
     , ("c", ⟨some 0⟩)
     ]

def testAddiUnknownOperand : Bool :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() : () -> i32\n\
  %u = \"test.test\"() : () -> i32\n\
  %c = \"arith.addi\"(%a, %u) : (i32, i32) -> i32\n\
}) : () -> ()"
  runConstantValuePropagation mlir
    #[ ("a", ⟨some 0⟩)
     , ("u", ⟨none⟩)
     , ("c", ⟨none⟩)
     ]

def testMuliUnknownOperand : Bool :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() : () -> i32\n\
  %u = \"test.test\"() : () -> i32\n\
  %c = \"arith.muli\"(%a, %u) : (i32, i32) -> i32\n\
}) : () -> ()"
  runConstantValuePropagation mlir
    #[ ("a", ⟨some 0⟩)
     , ("u", ⟨none⟩)
     , ("c", ⟨none⟩)
     ]

def testAndiUnknownOperand : Bool :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() : () -> i32\n\
  %u = \"test.test\"() : () -> i32\n\
  %c = \"arith.andi\"(%a, %u) : (i32, i32) -> i32\n\
}) : () -> ()"
  runConstantValuePropagation mlir
    #[ ("a", ⟨some 0⟩)
     , ("u", ⟨none⟩)
     , ("c", ⟨none⟩)
     ]

def testSubiUnknownOperand : Bool :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  %a = \"arith.constant\"() : () -> i32\n\
  %u = \"test.test\"() : () -> i32\n\
  %c = \"arith.subi\"(%a, %u) : (i32, i32) -> i32\n\
}) : () -> ()"
  runConstantValuePropagation mlir
    #[ ("a", ⟨some 0⟩)
     , ("u", ⟨none⟩)
     , ("c", ⟨none⟩)
     ]

def testSubiFoldNoUnderflow : Bool :=
  ConstantAnalysis.foldSubiConstants? 7 3 == some 4

def testSubiFoldUnderflowUnknown : Bool :=
  ConstantAnalysis.foldSubiConstants? 0 1 == none

#assert! testAddiAllConstant
#assert! testMuliAllConstant
#assert! testAndiAllConstant
#assert! testSubiAllConstant
#assert! testAddiUnknownOperand
#assert! testMuliUnknownOperand
#assert! testAndiUnknownOperand
#assert! testSubiUnknownOperand
#assert! testSubiFoldNoUnderflow
#assert! testSubiFoldUnderflowUnknown

