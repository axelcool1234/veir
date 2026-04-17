module

public import Veir.IR.Basic
public import Std.Data.HashSet.Basic
public import Std.Data.HashMap
open Std (HashMap)

namespace Veir
public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Pointer to a node in a dominance tree.
Contains a RegionPtr to indicate which dominance 
tree this node belongs to.
Contains an index which points to the DomTreeNode
in question.
-/
structure DomTreeNodePtr where
  region : RegionPtr
  index : Nat
deriving Inhabited, Repr, DecidableEq, Hashable

/-- An MLIR block pointer with dominance information.
Contains its immediate dominator and the children it dominates.
Invariants:
If the firstChild is none, lastChild is none.
If firstChild is some, lastChild is some.
lastChild's sibling should always be none.
-/
structure DomTreeNode where
  block : BlockPtr
  iDom : Option DomTreeNodePtr
  firstChild : Option DomTreeNodePtr
  lastChild : Option DomTreeNodePtr
  sibling : Option DomTreeNodePtr
  deriving Inhabited, Repr

abbrev DomTree := Array DomTreeNode
abbrev DomContext := HashMap RegionPtr DomTree 

instance : Repr DomContext where
  reprPrec ctx prec := reprPrec (ctx.toList) prec

def DomTreeNode.empty (block : BlockPtr) : DomTreeNode :=
{
  block := block
  iDom := none
  firstChild := none
  lastChild := none
  sibling := none
}

def RegionPtr.getDomTree! (ptr : RegionPtr) (ctx : DomContext) : DomTree := 
  ctx[ptr]!

def RegionPtr.newDomTreeNode! (ptr : RegionPtr) (block : BlockPtr) (ctx : DomContext) : DomContext := 
  ctx.modify ptr fun tree => tree.push (DomTreeNode.empty block)

def RegionPtr.getDomTreeSize! (ptr : RegionPtr) (ctx : DomContext) : Nat :=
  (ptr.getDomTree! ctx).size

def DomTreeNodePtr.getDomTree! (ptr : DomTreeNodePtr) (ctx : DomContext) : DomTree :=
  ptr.region.getDomTree! ctx

def DomTreeNodePtr.get! (ptr : DomTreeNodePtr) (ctx : DomContext) : DomTreeNode :=
  (ptr.getDomTree! ctx)[ptr.index]!

def DomTreeNodePtr.getBlock! (ptr : DomTreeNodePtr) (ctx : DomContext) : BlockPtr :=
  (ptr.get! ctx).block

def DomTreeNodePtr.getIDom! (ptr : DomTreeNodePtr) (ctx : DomContext) : Option DomTreeNodePtr :=
  (ptr.get! ctx).iDom

def DomTreeNodePtr.getFirstChild! (ptr : DomTreeNodePtr) (ctx : DomContext) : Option DomTreeNodePtr :=
  (ptr.get! ctx).firstChild

def DomTreeNodePtr.getLastChild! (ptr : DomTreeNodePtr) (ctx : DomContext) : Option DomTreeNodePtr :=
  (ptr.get! ctx).lastChild

def DomTreeNodePtr.getSibling! (ptr : DomTreeNodePtr) (ctx : DomContext) : Option DomTreeNodePtr :=
  (ptr.get! ctx).sibling

def DomTreeNodePtr.getLastChildSibling! (ptr : DomTreeNodePtr) (ctx : DomContext) : Option DomTreeNodePtr :=
  (ptr.getLastChild! ctx).get!.getSibling! ctx

def DomTreeNodePtr.isLeaf! (ptr : DomTreeNodePtr) (ctx : DomContext) : Bool :=
  (ptr.getFirstChild! ctx).isNone

def DomContext.modifyNode! (ctx : DomContext) (ptr : DomTreeNodePtr) (f : DomTreeNode -> DomTreeNode) : DomContext :=
  ctx.modify ptr.region fun tree => tree.set! ptr.index (f (ptr.get! ctx))

def DomTreeNodePtr.addChild! (parent child : DomTreeNodePtr) (ctx : DomContext) : DomContext := 
  let parentNode := parent.get! ctx 

  if (child.getSibling! ctx).isSome then 
    panic! "cannot add child that already has siblings"
  else if !(parent.isLeaf! ctx) && 
          (parent.getLastChildSibling! ctx).isSome then 
    panic! "sibling of last child must be none" 
  else
    match parentNode.lastChild with
    | none => ctx.modifyNode! parent ({ · with firstChild := some child, lastChild := some child })
    | some last => 
      let ctx := ctx.modifyNode! last ({ · with sibling := some child })
      ctx.modifyNode! parent ({ · with lastChild := some child })

def DomTreeNodePtr.removeChild! (parent child : DomTreeNodePtr) (ctx : DomContext) : DomContext := Id.run do
  let childSibling := child.getSibling! ctx
  let parentLast := parent.getLastChild! ctx
  let parentFirst := parent.getFirstChild! ctx

  -- Check invariants
  if !(parent.isLeaf! ctx) && 
     (parent.getLastChildSibling! ctx).isSome then 
    panic! "sibling of last child must be none" 
  if childSibling.isNone ≠ (parentLast = some child) then
      panic! "parent's last child is not the same as the last sibling"  
  
  -- Special case: child being removed is first child in sibling list
  if parentFirst = child then
    if parentFirst = parentLast then
      ctx.modifyNode! parent ({ · with firstChild := none, lastChild := none })
    else
      let ctx := ctx.modifyNode! parent fun n => { n with firstChild := childSibling }
      ctx.modifyNode! child ({ · with sibling := none })
  else -- Iterate
    match parentFirst with
    | none => panic! "Not in immediate dominator children list!"
    | some prev => 
        let mut prev := prev
        let mut curr := prev.getSibling! ctx 
        while curr != child do
          match curr with
          | none => panic! "Not in immediate dominator children list!"
          | some sibling => prev := sibling; curr := (sibling.getSibling! ctx) 
        let ctx := ctx.modifyNode! prev fun n => { n with sibling := childSibling }
        if childSibling.isSome then
          ctx.modifyNode! child ({ · with sibling := none })
        else
          ctx.modifyNode! parent ({ · with lastChild := prev })

def DomTreeNodePtr.setIDom! (ptr newIDom : DomTreeNodePtr) (ctx : DomContext) : DomContext := Id.run do
  match ptr.getIDom! ctx with
  | none =>
    let ctx := ctx.modifyNode! ptr ({ · with iDom := some newIDom })
    newIDom.addChild! ptr ctx
  | some iDom =>
    if iDom = newIDom then 
      return ctx
    else
      let ctx := iDom.removeChild! ptr ctx
      let ctx := ctx.modifyNode! ptr ({ · with iDom := some newIDom })
      newIDom.addChild! ptr ctx

def intersect (block1 block2 : BlockPtr) (idx : HashMap BlockPtr DomTreeNodePtr) (domCtx : DomContext) : BlockPtr := Id.run do 
  let mut finger1 := idx[block1]!
  let mut finger2 := idx[block2]!
  while finger1 != finger2 do
    while finger1.index < finger2.index do
      finger1 := (finger1.getIDom! domCtx).get! 
    while finger2.index < finger1.index do  
      finger2 := (finger2.getIDom! domCtx).get! 
  return (finger1.getBlock! domCtx)

/-- Constructs a dominance tree for a region.
Uses the Cooper Harvey Kennedy algorithm.
-/
def RegionPtr.computeDomTree! (ptr : RegionPtr) (domCtx : DomContext) (irCtx : IRContext OpInfo) : DomContext := Id.run do
  -- Postorder traversal of blocks, insert into DomTree (which is just an array!) 
  let mut postOrderIndex : HashMap BlockPtr DomTreeNodePtr := {}
  let mut domCtx := domCtx.insert ptr #[]
  match (ptr.get! irCtx).firstBlock with
  | none => return domCtx
  | some entry =>
    let mut worklist : Array (Option BlockPtr × Bool) := #[(entry, false)]
    let mut seen : Std.HashSet BlockPtr := {}
    while not worklist.isEmpty do
      let (block, visited) := worklist.back!
      worklist := worklist.pop 
      match block with
      | none => continue
      | some block =>
        if visited then 
          postOrderIndex := postOrderIndex.insert block { region := ptr, index := (ptr.getDomTreeSize! domCtx) }
          domCtx := ptr.newDomTreeNode! block domCtx 
        else if seen.contains block then
          continue
        else
          seen := seen.insert block
          worklist := worklist.push (block, true) 
          let op := (block.get! irCtx).lastOp.get!
          for childIdx in [0 :op.getNumSuccessors! irCtx] do
            worklist := worklist.push ((op.getSuccessor! irCtx childIdx), false)

    -- Give entry block its iDom (which is itself)
    let entryPtr := postOrderIndex[entry]!
    domCtx := DomContext.modifyNode! domCtx entryPtr ({ · with iDom := some entryPtr })

    -- Iterate backwards through the DomTree (reverse postorder traversal)
    let mut changed := true
    while changed do
      let domTree := ptr.getDomTree! domCtx
      changed := false
      for node in domTree.reverse do
        -- Entry block was already given its iDom
        if node.block = entry then
          continue
        let mut pred := (node.block.get! irCtx).firstUse
        let mut newIDom : Option BlockPtr := none
        while pred.isSome do
          let predBlockPtr := ((pred.get!.get! irCtx).owner.get! irCtx).parent.get! 
          if postOrderIndex.contains predBlockPtr then
            if domTree[postOrderIndex[predBlockPtr]!.index]!.iDom.isSome then
              newIDom := match newIDom with
                | none => some predBlockPtr
                | some curr => some (intersect predBlockPtr curr postOrderIndex domCtx)
          pred := (pred.get!.get! irCtx).nextUse 
        -- Skip if this block has no uses (and thus no "newIDom")
        if newIDom.isNone then
          continue
        let nodePtr := postOrderIndex[node.block]!
        let newIDomPtr := postOrderIndex[newIDom.get!]!
        if (nodePtr.getIDom! domCtx) != newIDomPtr then
          domCtx := nodePtr.setIDom! newIDomPtr domCtx
          changed := true
    domCtx
