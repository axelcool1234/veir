import Veir.IR.Basic
import Veir.OpCode
import Veir.Parser.MlirParser
import Veir.IR.Dominance
import Veir.Printer

open Veir
open Veir.Parser

/- 
  Macro to simplify test assertions. Wraps the test in #guard_msgs and #eval!,
  expecting the result to be `true`.
-/
macro "#assert! " e:term : command =>
  `(command| /--
    info: true
  -/
  #guard_msgs in
  #eval! $e)

/- 
  Parse MLIR, compute the dom tree, and return the context + region pointer + dom context.
  Returns none on any parse/IR failure to keep tests boolean.
-/
def buildDom (s : String) : Option (IRContext OpCode × RegionPtr × DomContext) :=
  match IRContext.create OpCode with
  | none => none
  | some (ctx, _) =>
    match ParserState.fromInput (s.toByteArray) with
    | .error e => dbg_trace e; none
    | .ok parser =>
      match (parseOp none).run (MlirParserState.fromContext ctx) parser with
      | .error e => dbg_trace e; none
      | .ok (op, state, _) =>
        let regionPtr := op.getRegion! state.ctx 0
        let domCtx := regionPtr.computeDomTree! ({} : DomContext) state.ctx
        some (state.ctx, regionPtr, domCtx)

/- 
  Enumerate blocks in a region in order using the block linked list.
-/
def regionBlocks (ctx : IRContext OpCode) (regionPtr : RegionPtr) : Array BlockPtr := Id.run do
  let mut out : Array BlockPtr := #[]
  let mut curr := (regionPtr.get! ctx).firstBlock
  while curr.isSome do
    let b := curr.get!
    out := out.push b
    curr := (b.get! ctx).next
  return out

/- 
  Compare arrays as sets (ignores order, requires same cardinality).
-/
def sameSet (a b : Array BlockPtr) : Bool :=
  a.size == b.size && a.all (fun x => b.contains x) && b.all (fun x => a.contains x)

/- 
  Look up the immediate dominator block for a given block.
-/
def iDomBlock (domCtx : DomContext) (regionPtr : RegionPtr) (blockPtr : BlockPtr) : BlockPtr := Id.run do
  let tree := regionPtr.getDomTree! domCtx
  let mut i := 0
  let mut nodePtr : Option DomTreeNodePtr := none
  while i < tree.size do
    if tree[i]!.block == blockPtr then
      nodePtr := some { region := regionPtr, index := i }
      break
    i := i + 1
  let node := nodePtr.get!
  let iDomPtr := (node.getIDom! domCtx).get!
  return iDomPtr.getBlock! domCtx

/- 
  Collect the children of a dominator tree node as blocks.
-/
def childrenBlocks (domCtx : DomContext) (regionPtr : RegionPtr) (blockPtr : BlockPtr) : Array BlockPtr := Id.run do
  let tree := regionPtr.getDomTree! domCtx
  let mut i := 0
  let mut nodePtr : Option DomTreeNodePtr := none
  while i < tree.size do
    if tree[i]!.block == blockPtr then
      nodePtr := some { region := regionPtr, index := i }
      break
    i := i + 1
  let mut children : Array BlockPtr := #[]
  let mut child := (nodePtr.get!).getFirstChild! domCtx
  while child.isSome do
    let childPtr := child.get!
    children := children.push (childPtr.getBlock! domCtx)
    child := childPtr.getSibling! domCtx
  return children

/- 
  Check a list of (blockIndex, expectedIDomIndex) pairs by comparing each block’s
  computed immediate dominator with the expected block. Returns true only if all pairs match.
-/
def checkIDoms (blockPtrs : Array BlockPtr) (domCtx : DomContext) (regionPtr : RegionPtr)
    (pairs : Array (Nat × Nat)) : Bool :=
  pairs.all (fun pair =>
    let blockPtr := blockPtrs[pair.fst]!
    let expect := blockPtrs[pair.snd]!
    iDomBlock domCtx regionPtr blockPtr == expect)

/- 
  Check a list of (blockIndex, expectedChildrenIndices) pairs by collecting the block’s
  dominator-tree children and comparing as a set (order-independent). Returns true only if all match.
-/
def checkChildren (blockPtrs : Array BlockPtr) (domCtx : DomContext) (regionPtr : RegionPtr)
    (pairs : Array (Nat × Array Nat)) : Bool :=
  pairs.all (fun pair =>
    let blockPtr := blockPtrs[pair.fst]!
    let expected := pair.snd.map (fun i => blockPtrs[i]!)
    sameSet (childrenBlocks domCtx regionPtr blockPtr) expected)

/- 
  Parse MLIR and check both idom pairs and child pairs against the computed dom tree.
-/
def checkDom (mlir : String) (iDomPairs : Array (Nat × Nat))
    (childPairs : Array (Nat × Array Nat)) : Bool :=
  match buildDom mlir with
  | none => false
  | some (ctx, regionPtr, domCtx) =>
    let blockPtrs := regionBlocks ctx regionPtr
    let okIDom := checkIDoms blockPtrs domCtx regionPtr iDomPairs
    let okChildren := checkChildren blockPtrs domCtx regionPtr childPairs
    okIDom && okChildren


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
def testDomLoop : Bool :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1] : () -> ()\n\
^bb1:\n\
  \"test.test\"() [^bb2] : () -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb1] : () -> ()\n\
}) : () -> ()"
  checkDom mlir #[(0,0), (1,0), (2,1)] #[(0, #[1]), (1, #[2]), (2, #[])]

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
def testDomDiamond : Bool :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1, ^bb2] : () -> ()\n\
^bb1:\n\
  \"test.test\"() [^bb3] : () -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb3] : () -> ()\n\
^bb3:\n\
  \"test.test\"() : () -> ()\n\
}) : () -> ()"
  checkDom mlir #[(0,0), (1,0), (2,0), (3,0)] #[(0, #[1,2,3]), (1, #[]), (2, #[]), (3, #[])]

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
def testDomLine : Bool :=
  let mlir := "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1] : () -> ()\n\
^bb1:\n\
  \"test.test\"() [^bb2] : () -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb3] : () -> ()\n\
^bb3:\n\
  \"test.test\"() : () -> ()\n\
}) : () -> ()"
  checkDom mlir #[(0,0), (1,0), (2,1), (3,2)] #[(0, #[1]), (1, #[2]), (2, #[3]), (3, #[])]

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
def testDomIfLoopIf : Bool :=
  let mlir := "\"builtin.module\"() ({\n\
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
  \"test.test\"() [] : () -> ()\n\
}) : () -> ()"
  checkDom mlir
    #[(0,0), (1,0), (2,0), (3,2), (4,2), (5,1), (6,2), (7, 0)]
    #[(0, #[1,2,7]), (1, #[5]), (2, #[3,4,6]), (3, #[]), (4, #[]), (5, #[]), (6, #[]), (7, #[])]

#assert! testDomLoop
#assert! testDomDiamond
#assert! testDomLine
#assert! testDomIfLoopIf
