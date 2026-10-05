module

public import Veir.Analysis.DataFlow.DominanceAnalysis
public import Veir.Dominance.Lemmas.Path
public import Veir.Verifier

import Std.Tactic.Do
import all Veir.Analysis.DataFlow.Facts
import all Veir.Dominance.Basic
import all Veir.IR.Basic
import all Veir.IR.Dominance

public section

namespace Veir

/-!
# Dominance analysis correctness

This module connects the dense RPO-indexed `DominanceValue` used by the CHK
implementation to VeIR's path-based dominance semantics. It deliberately does
not introduce a second CFG semantics.
-/

namespace DominanceValue

/--
The abstract value contains the semantic immediate dominator of every block
that has one. `reversePostOrder` supplies the representation map from dense
indices to the blocks governed by `BlockPtr.ImmediateDominatorInSSACFGRegion`.
-/
def SoundForRegion [HasOpInfo OpInfo]
    (value : DominanceValue blockCount)
    (reversePostOrder : Vector BlockPtr blockCount)
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo) : Prop :=
  ∀ blockIndex dominatorIndex,
    (reversePostOrder.get dominatorIndex).ImmediateDominatorInSSACFGRegion
      (reversePostOrder.get blockIndex) region irCtx →
    (blockIndex, dominatorIndex) ∈ γ value

/-- An RPO index has an initialized working immediate dominator. -/
def Initialized (value : DominanceValue blockCount) (blockIndex : Fin blockCount) : Prop :=
  ∃ immediateDominator : Fin blockCount,
    value.get? blockIndex.val = some immediateDominator.val

/-- Every RPO index strictly before `blockIndex` is initialized. -/
def InitializedBefore
    (value : DominanceValue blockCount)
    (blockIndex : Fin blockCount) : Prop :=
  ∀ earlierIndex : Fin blockCount, earlierIndex < blockIndex → Initialized value earlierIndex

/--
The initialized entries form a closed, descending working forest. Following a
working-parent edge preserves every semantic dominator whose RPO index is
strictly earlier than the child. The strictness matters: a block dominates
itself, but generally does not dominate its own working parent.
-/
structure WorkingForestForRegion [HasOpInfo OpInfo]
    (value : DominanceValue blockCount)
    (reversePostOrder : Vector BlockPtr blockCount)
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo) : Prop where
  not_bottom : value ≠ ⊥
  parent_decreases : ∀ (blockIndex immediateDominator : Fin blockCount),
    value.get? blockIndex.val = some immediateDominator.val →
    (blockIndex.val = 0 ∧ immediateDominator.val = 0) ∨
      immediateDominator < blockIndex
  parent_initialized : ∀ (blockIndex immediateDominator : Fin blockCount),
    value.get? blockIndex.val = some immediateDominator.val →
    Initialized value immediateDominator
  preserves_strict_dominators :
    ∀ (blockIndex immediateDominator dominatorIndex : Fin blockCount),
    value.get? blockIndex.val = some immediateDominator.val →
    dominatorIndex < blockIndex →
    (reversePostOrder.get dominatorIndex).DominatesInSSACFGRegion
      (reversePostOrder.get blockIndex) region irCtx →
    (reversePostOrder.get dominatorIndex).DominatesInSSACFGRegion
      (reversePostOrder.get immediateDominator) region irCtx

/-- Semantic dominators occur no later than dominated blocks in the RPO representation. -/
def OrderedForRegion [HasOpInfo OpInfo]
    (reversePostOrder : Vector BlockPtr blockCount)
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo) : Prop :=
  ∀ dominatorIndex dominatedIndex,
    (reversePostOrder.get dominatorIndex).DominatesInSSACFGRegion
      (reversePostOrder.get dominatedIndex) region irCtx →
    dominatorIndex ≤ dominatedIndex

/-- RPO indices uniquely identify the reachable blocks represented by a region value. -/
def InjectiveRPO (reversePostOrder : Vector BlockPtr blockCount) : Prop :=
  Function.Injective reversePostOrder.get

/-- Every block reachable from the entry has an index in the region's RPO representation. -/
def ReachableBlocksRepresented [HasOpInfo OpInfo]
    (reversePostOrder : Vector BlockPtr blockCount)
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo) : Prop :=
  ∀ block : BlockPtr,
    block.ReachableFromEntry region irCtx →
    ∃ blockIndex : Fin blockCount, reversePostOrder.get blockIndex = block

/-- The semantic obligations maintained while folding initialized predecessors. -/
structure PartialCandidateForBlock [HasOpInfo OpInfo]
    (value : DominanceValue blockCount)
    (reversePostOrder : Vector BlockPtr blockCount)
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo)
    (blockIndex immediateDominator : Fin blockCount) : Prop where
  initialized : Initialized value immediateDominator
  preserves_strict_dominators : ∀ dominatorIndex : Fin blockCount,
    dominatorIndex < blockIndex →
    (reversePostOrder.get dominatorIndex).DominatesInSSACFGRegion
      (reversePostOrder.get blockIndex) region irCtx →
    (reversePostOrder.get dominatorIndex).DominatesInSSACFGRegion
      (reversePostOrder.get immediateDominator) region irCtx
  contains_immediate_dominator : ∀ dominatorIndex : Fin blockCount,
    (reversePostOrder.get dominatorIndex).ImmediateDominatorInSSACFGRegion
      (reversePostOrder.get blockIndex) region irCtx →
    dominatorIndex ≤ immediateDominator

/-- The obligations an executable CHK candidate must satisfy before refinement. -/
structure UpdateCandidateForBlock [HasOpInfo OpInfo]
    (value : DominanceValue blockCount)
    (reversePostOrder : Vector BlockPtr blockCount)
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo)
    (blockIndex immediateDominator : Fin blockCount)
    extends PartialCandidateForBlock value reversePostOrder region irCtx
      blockIndex immediateDominator where
  decreases :
    (blockIndex.val = 0 ∧ immediateDominator.val = 0) ∨
      immediateDominator < blockIndex

/-- A raw predecessor index denotes an actual CFG predecessor represented by the RPO. -/
def PredecessorIndexForBlock [HasOpInfo OpInfo]
    (reversePostOrder : Vector BlockPtr blockCount)
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo)
    (blockIndex : Fin blockCount)
    (predecessorIndex : Nat) : Prop :=
  ∃ predecessor : Fin blockCount,
    predecessor.val = predecessorIndex ∧
    ((reversePostOrder.get predecessor).get! irCtx.raw).parent = some region ∧
    reversePostOrder.get blockIndex ∈
      (reversePostOrder.get predecessor).getSuccessors! irCtx.raw

/-- Regard a dynamically sized RPO array as a vector at that same size. -/
def reversePostOrderVector (reversePostOrder : Array BlockPtr) :
    Vector BlockPtr reversePostOrder.size :=
  ⟨reversePostOrder, rfl⟩

@[simp]
theorem reversePostOrderVector_get
    (reversePostOrder : Array BlockPtr)
    (index : Fin reversePostOrder.size) :
    (reversePostOrderVector reversePostOrder).get index =
      reversePostOrder[index.val] := by
  unfold reversePostOrderVector Vector.get
  apply getElem_congr_idx
  rfl

/-- The graph-order properties that the concrete DFS collector must establish. -/
structure ReversePostOrderForRegion
    (reversePostOrder : Array BlockPtr) [NeZero reversePostOrder.size]
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode) : Prop where
  entry_is_first : (region.get! irCtx.raw).firstBlock = some reversePostOrder[0]!
  blocks_parent : ∀ blockIndex : Fin reversePostOrder.size,
    ((reversePostOrder[blockIndex.val]).get! irCtx.raw).parent = some region
  injective_rpo : Function.Injective fun blockIndex : Fin reversePostOrder.size =>
    reversePostOrder[blockIndex.val]
  earlier_predecessor : ∀ blockIndex : Fin reversePostOrder.size,
    blockIndex.val ≠ 0 →
    ∃ predecessorIndex : Fin reversePostOrder.size,
      predecessorIndex < blockIndex ∧
      reversePostOrder[blockIndex.val] ∈
        reversePostOrder[predecessorIndex.val].getSuccessors! irCtx.raw

/-! ## Concrete DFS collector invariant -/

/-- Every successor returned for an in-bounds block is itself in bounds. -/
theorem BlockPtr.successor_inBounds
    (irCtx : WfIRContext OpCode)
    {block successor : BlockPtr}
    (blockInBounds : block.InBounds irCtx.raw)
    (successorMem : successor ∈ block.getSuccessors! irCtx.raw) :
    successor.InBounds irCtx.raw := by
  simp only [BlockPtr.getSuccessors!] at successorMem
  split at successorMem
  · simp at successorMem
  · rename_i terminator terminatorEq
    rw [OperationPtr.getSuccessors!.mem_iff_exists_index] at successorMem
    rcases successorMem with ⟨index, indexInBounds, successorEq⟩
    rw [← successorEq]
    have terminatorInBounds : terminator.InBounds irCtx.raw := by grind
    have operandInBounds :
        (terminator.getBlockOperand index).InBounds irCtx.raw := by
      apply OperationPtr.getBlockOperand_inBounds terminator terminatorInBounds index
      simpa only [OperationPtr.getNumSuccessors!_eq_getNumSuccessors
        terminatorInBounds] using indexInBounds
    have fieldsInBounds := irCtx.wellFormed.inBounds
    simpa only [OperationPtr.getSuccessor!, BlockOperandPtr.get!,
      OperationPtr.getBlockOperand] using
        BlockOperandPtr.value!_inBounds
          (operand := terminator.getBlockOperand index)
          fieldsInBounds operandInBounds

/-- `first` occurs strictly before `second` in a list. -/
def List.Before {T : Type} (first second : T) (list : List T) : Prop :=
  ∃ before middle after,
    list = before ++ first :: middle ++ second :: after

theorem List.Before.append {T : Type} {first second : T} {list : List T}
    (before : List.Before first second list) (suffix : List T) :
    List.Before first second (list ++ suffix) := by
  obtain ⟨beforeList, middle, tail, rfl⟩ := before
  refine ⟨beforeList, middle, tail ++ suffix, ?_⟩
  simp only [List.append_assoc, List.cons_append]

theorem List.Before.append_right {T : Type} {first second : T} {list : List T}
    (firstMem : first ∈ list) : List.Before first second (list ++ [second]) := by
  rw [List.mem_iff_append] at firstMem
  obtain ⟨beforeList, suffix, rfl⟩ := firstMem
  refine ⟨beforeList, suffix, [], ?_⟩
  simp

theorem List.Before.reverse {T : Type} {first second : T} {list : List T}
    (before : List.Before first second list) :
    List.Before second first list.reverse := by
  obtain ⟨beforeList, middle, after, rfl⟩ := before
  refine ⟨after.reverse, middle.reverse, beforeList.reverse, ?_⟩
  simp [List.reverse_append, List.reverse_cons, List.append_assoc]

theorem List.Before.exists_indices {T : Type} {first second : T} {list : List T}
    (before : List.Before first second list) :
    ∃ (firstIndex secondIndex : Nat)
        (firstInBounds : firstIndex < list.length)
        (secondInBounds : secondIndex < list.length),
      firstIndex < secondIndex ∧
        list[firstIndex] = first ∧ list[secondIndex] = second := by
  obtain ⟨beforeList, middle, after, rfl⟩ := before
  refine ⟨beforeList.length, beforeList.length + 1 + middle.length,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp only [List.length_append, List.length_cons]
    omega
  · omega
  · simp
  · rw [List.getElem_append]
    split
    · rename_i indexBeforePrefix
      simp at indexBeforePrefix
      omega
    · rename_i indexAfterPrefix
      have indexEq : beforeList.length + 1 + middle.length =
          (beforeList ++ first :: middle).length := by
        simp only [List.length_append, List.length_cons]
        omega
      simp [indexEq]

theorem array_get_injective_of_toList_nodup
    (array : Array T) (nodup : array.toList.Nodup) :
    Function.Injective fun index : Fin array.size => array[index.val] := by
  intro index1 index2 equal
  apply Fin.eq_of_val_eq
  apply nodup.eq_of_getElem_eq
    (by simp [index1.isLt]) (by simp [index2.isLt])
  simpa only [Array.getElem_toList] using equal

theorem array_reverse_toList_nodup
    (array : Array T) (nodup : array.toList.Nodup) :
    array.reverse.toList.Nodup := by
  rw [Array.toList_reverse, List.nodup_iff_pairwise_ne, List.pairwise_reverse]
  exact (List.nodup_iff_pairwise_ne.mp nodup).imp fun different => different.symm

/-- The block pointers represented by DFS stack frames, from leaf to root. -/
def dfsStackBlocks (stack : List (BlockPtr × Nat)) : List BlockPtr :=
  stack.map Prod.fst

/-- The completed blocks followed by the active DFS path. -/
def dfsCollectorBlocks
    (postOrder : Array BlockPtr) (stack : List (BlockPtr × Nat)) : List BlockPtr :=
  postOrder.toList ++ dfsStackBlocks stack

/-- Adjacent stack frames are connected by a DFS tree edge. -/
def DFSStackPath (irCtx : WfIRContext OpCode) : List (BlockPtr × Nat) → Prop
  | [] | [_] => True
  | child :: parent :: tail =>
      child.1 ∈ parent.1.getSuccessors! irCtx.raw ∧
        DFSStackPath irCtx (parent :: tail)

/-- Every completed non-entry block has a DFS parent that finishes later. -/
def DFSCompletedHavePredecessor
    (entry : BlockPtr)
    (postOrder : Array BlockPtr)
    (stack : List (BlockPtr × Nat))
    (irCtx : WfIRContext OpCode) : Prop :=
  ∀ block, block ∈ postOrder → block ≠ entry →
    ∃ predecessor,
      block ∈ predecessor.getSuccessors! irCtx.raw ∧
        (predecessor ∈ dfsStackBlocks stack ∨
          List.Before block predecessor postOrder.toList)

/-- The semantic state maintained by the concrete iterative DFS. -/
structure DFSCollectorInvariant
    (entry : BlockPtr)
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (postOrder : Array BlockPtr)
    (stack : List (BlockPtr × Nat))
    (seen : Std.HashSet BlockPtr) : Prop where
  cursors_valid : ∀ frame ∈ stack,
    frame.2 ≤ (frame.1.getSuccessors! irCtx.raw).size
  stack_path : DFSStackPath irCtx stack
  blocks_nodup : (dfsCollectorBlocks postOrder stack).Nodup
  seen_iff : ∀ block,
    seen.contains block = true ↔ block ∈ dfsCollectorBlocks postOrder stack
  processed_successors_seen : ∀ frame ∈ stack,
    ∀ successorIndex, successorIndex < frame.2 →
      seen.contains (frame.1.getSuccessors! irCtx.raw)[successorIndex]! = true
  completed_successors_seen : ∀ block ∈ postOrder,
    ∀ successor ∈ block.getSuccessors! irCtx.raw,
      seen.contains successor = true
  blocks_valid : ∀ block, block ∈ dfsCollectorBlocks postOrder stack →
    block.InBounds irCtx.raw ∧ (block.get! irCtx.raw).parent = some region
  entry_last : (dfsCollectorBlocks postOrder stack).getLast? = some entry
  completed_have_predecessor :
    DFSCompletedHavePredecessor entry postOrder stack irCtx

theorem DFSCollectorInvariant.init
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (regionInBounds : region.InBounds irCtx.raw)
    (entry : BlockPtr)
    (entryEq : (region.get! irCtx.raw).firstBlock = some entry) :
    DFSCollectorInvariant entry region irCtx #[] [(entry, 0)]
      ({entry} : Std.HashSet BlockPtr) := by
  have entryInBounds : entry.InBounds irCtx.raw := by grind
  have entryParent : (entry.get! irCtx.raw).parent = some region :=
    RegionPtr.firstBlock!_parent! regionInBounds irCtx.wellFormed entryEq
  constructor
  · simp
  · simp [DFSStackPath]
  · simp [dfsCollectorBlocks, dfsStackBlocks]
  · intro block
    simp [dfsCollectorBlocks, dfsStackBlocks]
    constructor <;> intro equality <;> exact equality.symm
  · simp
  · simp
  · intro block blockMem
    simp only [dfsCollectorBlocks, dfsStackBlocks, List.map_cons, List.map_nil,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at blockMem
    subst block
    exact ⟨entryInBounds, entryParent⟩
  · simp [dfsCollectorBlocks, dfsStackBlocks]
  · intro block blockMem blockNe
    simp at blockMem

theorem DFSCollectorInvariant.advance
    (invariant : DFSCollectorInvariant entry region irCtx postOrder
      ((block, successorIndex) :: stack) seen)
    (successorIndexInBounds :
      successorIndex < (block.getSuccessors! irCtx.raw).size)
    (successorSeen :
      seen.contains (block.getSuccessors! irCtx.raw)[successorIndex]! = true) :
    DFSCollectorInvariant entry region irCtx postOrder
      ((block, successorIndex + 1) :: stack) seen := by
  constructor
  · intro frame frameMem
    simp only [List.mem_cons] at frameMem
    rcases frameMem with rfl | frameMem
    · dsimp only
      omega
    · exact invariant.cursors_valid frame (by simp [frameMem])
  · cases stack with
    | nil => simp [DFSStackPath]
    | cons parent stack =>
      simpa only [DFSStackPath] using invariant.stack_path
  · simpa only [dfsCollectorBlocks, dfsStackBlocks, List.map_cons,
      Prod.fst] using invariant.blocks_nodup
  · intro queriedBlock
    simpa only [dfsCollectorBlocks, dfsStackBlocks, List.map_cons,
      Prod.fst] using invariant.seen_iff queriedBlock
  · intro frame frameMem queriedIndex queriedBefore
    simp only [List.mem_cons] at frameMem
    rcases frameMem with rfl | frameMem
    · by_cases oldIndex : queriedIndex < successorIndex
      · exact invariant.processed_successors_seen (block, successorIndex) (by simp)
          queriedIndex oldIndex
      · have currentIndex : queriedIndex = successorIndex := by omega
        subst queriedIndex
        exact successorSeen
    · exact invariant.processed_successors_seen frame (by simp [frameMem])
        queriedIndex queriedBefore
  · exact invariant.completed_successors_seen
  · intro queriedBlock queriedMem
    apply invariant.blocks_valid queriedBlock
    simpa only [dfsCollectorBlocks, dfsStackBlocks, List.map_cons,
      Prod.fst] using queriedMem
  · simpa only [dfsCollectorBlocks, dfsStackBlocks, List.map_cons,
      Prod.fst] using invariant.entry_last
  · simpa only [DFSCompletedHavePredecessor, dfsStackBlocks,
      List.map_cons, Prod.fst] using invariant.completed_have_predecessor

theorem DFSCollectorInvariant.push
    (ctxVerified : irCtx.Verified root)
    (invariant : DFSCollectorInvariant entry region irCtx postOrder
      ((block, successorIndex) :: stack) seen)
    (successorIndexInBounds :
      successorIndex < (block.getSuccessors! irCtx.raw).size)
    (successorNotSeen : seen.contains successor = false)
    (successorEq :
      (block.getSuccessors! irCtx.raw)[successorIndex] = successor) :
    DFSCollectorInvariant entry region irCtx postOrder
      ((successor, 0) :: (block, successorIndex + 1) :: stack)
      (seen.insert successor) := by
  have successorMem : successor ∈ block.getSuccessors! irCtx.raw := by
    rw [← successorEq]
    exact Array.getElem_mem _
  have blockValid := invariant.blocks_valid block (by
    simp [dfsCollectorBlocks, dfsStackBlocks])
  have successorInBounds :=
    BlockPtr.successor_inBounds irCtx blockValid.1 successorMem
  have successorParent :=
    ctxVerified.successor_parent blockValid.1 blockValid.2 successorMem
  have successorNotCollected :
      successor ∉ dfsCollectorBlocks postOrder ((block, successorIndex) :: stack) := by
    intro successorMem
    have seenTrue := (invariant.seen_iff successor).2 successorMem
    rw [successorNotSeen] at seenTrue
    contradiction
  constructor
  · intro frame frameMem
    simp only [List.mem_cons] at frameMem
    rcases frameMem with rfl | frameMem
    · simp
    · rcases frameMem with rfl | frameMem
      · dsimp only
        omega
      · exact invariant.cursors_valid frame (by simp [frameMem])
  · refine ⟨successorMem, ?_⟩
    cases stack <;> simpa [DFSStackPath] using invariant.stack_path
  · unfold dfsCollectorBlocks dfsStackBlocks at successorNotCollected ⊢
    simp only [List.map_cons]
    have oldNodup := invariant.blocks_nodup
    unfold dfsCollectorBlocks dfsStackBlocks at oldNodup
    simp only [List.map_cons] at oldNodup
    rw [List.nodup_append] at oldNodup ⊢
    rcases oldNodup with ⟨postNodup, stackNodup, disjoint⟩
    constructor
    · exact postNodup
    · constructor
      · apply List.nodup_cons.mpr
        constructor
        · intro successorMem
          exact successorNotCollected (by simp [successorMem])
        · exact stackNodup
      · intro postBlock postBlockMem stackBlock stackBlockMem equal
        simp only [List.mem_cons] at stackBlockMem
        rcases stackBlockMem with rfl | stackBlockMem
        · apply successorNotCollected
          simp only [List.mem_append]
          exact Or.inl (equal ▸ postBlockMem)
        · apply disjoint postBlock postBlockMem stackBlock
            (List.mem_cons.mpr stackBlockMem) equal
  · intro queriedBlock
    rw [Std.HashSet.contains_insert]
    simp only [Bool.or_eq_true, beq_iff_eq]
    rw [invariant.seen_iff]
    simp only [dfsCollectorBlocks, dfsStackBlocks, List.map_cons,
      List.mem_append, List.mem_cons]
    grind
  · intro frame frameMem queriedIndex queriedBefore
    simp only [List.mem_cons] at frameMem
    rcases frameMem with rfl | frameMem
    · simp at queriedBefore
    · rcases frameMem with rfl | frameMem
      · rw [Std.HashSet.contains_insert]
        by_cases oldIndex : queriedIndex < successorIndex
        · have oldSeen := invariant.processed_successors_seen
              (block, successorIndex) (by simp) queriedIndex oldIndex
          simp only [oldSeen, Bool.or_true]
        · have currentIndex : queriedIndex = successorIndex := by omega
          subst queriedIndex
          rw [getElem!_pos (block.getSuccessors! irCtx.raw) successorIndex
            successorIndexInBounds, successorEq]
          simp
      · rw [Std.HashSet.contains_insert]
        have oldSeen := invariant.processed_successors_seen frame (by simp [frameMem])
          queriedIndex queriedBefore
        simp only [oldSeen, Bool.or_true]
  · intro completed completedMem queriedSuccessor queriedSuccessorMem
    rw [Std.HashSet.contains_insert]
    have oldSeen := invariant.completed_successors_seen completed completedMem
      queriedSuccessor queriedSuccessorMem
    simp only [oldSeen, Bool.or_true]
  · intro queriedBlock queriedMem
    by_cases successorIsQueried : queriedBlock = successor
    · subst queriedBlock
      exact ⟨successorInBounds, successorParent⟩
    · apply invariant.blocks_valid queriedBlock
      simp only [dfsCollectorBlocks, dfsStackBlocks, List.map_cons,
        List.mem_append, List.mem_cons] at queriedMem ⊢
      grind
  · have sameLast :
        (dfsCollectorBlocks postOrder
          ((successor, 0) :: (block, successorIndex + 1) :: stack)).getLast? =
        (dfsCollectorBlocks postOrder
          ((block, successorIndex) :: stack)).getLast? := by
      simp [dfsCollectorBlocks, dfsStackBlocks, List.getLast?_append]
    rw [sameLast]
    exact invariant.entry_last
  · intro completed completedMem completedNe
    obtain ⟨predecessor, edge, onStack | before⟩ :=
      invariant.completed_have_predecessor completed completedMem completedNe
    · refine ⟨predecessor, edge, Or.inl ?_⟩
      change predecessor ∈ successor ::
        dfsStackBlocks ((block, successorIndex) :: stack)
      exact List.mem_cons.mpr (Or.inr onStack)
    · exact ⟨predecessor, edge, Or.inr before⟩

theorem DFSCollectorInvariant.pop
    (invariant : DFSCollectorInvariant entry region irCtx postOrder
      ((block, successorIndex) :: stack) seen)
    (successorsDone : (block.getSuccessors! irCtx.raw).size ≤ successorIndex) :
    DFSCollectorInvariant entry region irCtx (postOrder.push block) stack seen := by
  have collectorBlocksEq :
      dfsCollectorBlocks (postOrder.push block) stack =
        dfsCollectorBlocks postOrder ((block, successorIndex) :: stack) := by
    simp [dfsCollectorBlocks, dfsStackBlocks, Array.toList_push,
      List.append_assoc]
  have blockNotCompleted : block ∉ postOrder := by
    intro blockMem
    have nodup := invariant.blocks_nodup
    unfold dfsCollectorBlocks dfsStackBlocks at nodup
    simp only [List.map_cons, List.nodup_append] at nodup
    exact nodup.2.2 block
      (by simpa only [Array.mem_toList_iff] using blockMem)
      block (by simp) rfl
  constructor
  · intro frame frameMem
    exact invariant.cursors_valid frame (by simp [frameMem])
  · cases stack with
    | nil => trivial
    | cons parent stack => exact invariant.stack_path.2
  · rw [collectorBlocksEq]
    exact invariant.blocks_nodup
  · intro queriedBlock
    rw [collectorBlocksEq]
    exact invariant.seen_iff queriedBlock
  · intro frame frameMem queriedIndex queriedBefore
    exact invariant.processed_successors_seen frame (by simp [frameMem])
      queriedIndex queriedBefore
  · intro completed completedMem queriedSuccessor queriedSuccessorMem
    rw [Array.mem_push] at completedMem
    rcases completedMem with oldCompleted | rfl
    · exact invariant.completed_successors_seen completed oldCompleted
        queriedSuccessor queriedSuccessorMem
    · obtain ⟨queriedIndex, queriedIndexInBounds, queriedEq⟩ :=
        Array.mem_iff_getElem.mp queriedSuccessorMem
      rw [← queriedEq]
      have oldSeen := invariant.processed_successors_seen
        (completed, successorIndex) (by simp) queriedIndex (by omega)
      rw [getElem!_pos (completed.getSuccessors! irCtx.raw) queriedIndex
        queriedIndexInBounds] at oldSeen
      exact oldSeen
  · intro queriedBlock queriedMem
    apply invariant.blocks_valid queriedBlock
    rw [← collectorBlocksEq]
    exact queriedMem
  · rw [collectorBlocksEq]
    exact invariant.entry_last
  · intro completed completedMem completedNe
    rw [Array.mem_push] at completedMem
    rcases completedMem with oldCompleted | rfl
    · obtain ⟨predecessor, edge, onStack | before⟩ :=
        invariant.completed_have_predecessor completed oldCompleted completedNe
      unfold dfsStackBlocks at onStack
      simp only [List.map_cons, List.mem_cons] at onStack
      rcases onStack with predecessorIsBlock | predecessorOnStack
      · subst predecessor
        refine ⟨block, edge, Or.inr ?_⟩
        simpa only [Array.toList_push] using
          List.Before.append_right
            (by simpa only [Array.mem_toList_iff] using oldCompleted)
      · exact ⟨predecessor, edge, Or.inl (by
          simpa only [dfsStackBlocks] using predecessorOnStack)⟩
      · exact ⟨predecessor, edge, Or.inr (by
          simpa only [Array.toList_push] using before.append [block])⟩
    · cases stack with
      | nil =>
        have blockIsEntry : completed = entry := by
          have entryLast := invariant.entry_last
          simpa [dfsCollectorBlocks, dfsStackBlocks, List.getLast?_append] using
            entryLast
        exact (completedNe blockIsEntry).elim
      | cons parent stack =>
        refine ⟨parent.1, ?_, Or.inl ?_⟩
        · exact invariant.stack_path.1
        · simp [dfsStackBlocks]

/-! ## DFS termination measure -/

def dfsBlockWork (irCtx : WfIRContext OpCode) (block : BlockPtr) : Nat :=
  (block.getSuccessors! irCtx.raw).size + 2

def dfsUnseenWork
    (irCtx : WfIRContext OpCode) (seen : Std.HashSet BlockPtr) : Nat :=
  irCtx.raw.blocks.keys.foldl (fun total block =>
    if seen.contains block then total else total + dfsBlockWork irCtx block) 0

def dfsStackWork
    (irCtx : WfIRContext OpCode) (stack : List (BlockPtr × Nat)) : Nat :=
  (stack.map fun frame =>
    ((frame.1.getSuccessors! irCtx.raw).size - frame.2) + 1).sum

def dfsMeasure
    (irCtx : WfIRContext OpCode)
    (seen : Std.HashSet BlockPtr)
    (stack : List (BlockPtr × Nat)) : Nat :=
  dfsUnseenWork irCtx seen + dfsStackWork irCtx stack

theorem dfsFoldWork_eq_sum
    (irCtx : WfIRContext OpCode)
    (seen : Std.HashSet BlockPtr)
    (blocks : List BlockPtr)
    (initial : Nat) :
    blocks.foldl (fun total block =>
      if seen.contains block then total else total + dfsBlockWork irCtx block) initial =
      initial + (blocks.map fun block =>
        if seen.contains block then 0 else dfsBlockWork irCtx block).sum := by
  induction blocks generalizing initial with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    split <;> simp_all [Nat.add_assoc]

theorem dfsKeys_nodup
    (blocks : Std.HashMap BlockPtr Block) : blocks.keys.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  apply blocks.distinct_keys.imp
  intro a b different
  exact fun equal => by simp [equal] at different

theorem dfsUnseenWork_insert
    (irCtx : WfIRContext OpCode)
    (seen : Std.HashSet BlockPtr)
    (block : BlockPtr)
    (blockIn : block ∈ irCtx.raw.blocks.keys)
    (notSeen : seen.contains block = false) :
    dfsUnseenWork irCtx (seen.insert block) + dfsBlockWork irCtx block =
      dfsUnseenWork irCtx seen := by
  unfold dfsUnseenWork
  rw [dfsFoldWork_eq_sum, dfsFoldWork_eq_sum]
  simp only [Nat.zero_add]
  suffices ∀ blocks : List BlockPtr, blocks.Nodup → block ∈ blocks →
      (blocks.map fun current =>
        if (seen.insert block).contains current then 0 else dfsBlockWork irCtx current).sum +
          dfsBlockWork irCtx block =
        (blocks.map fun current =>
          if seen.contains current then 0 else dfsBlockWork irCtx current).sum by
    exact this irCtx.raw.blocks.keys (dfsKeys_nodup irCtx.raw.blocks) blockIn
  intro blocks nodup blockIn
  induction blocks with
  | nil => simp_all
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [List.nodup_cons] at nodup
    simp only [List.mem_cons] at blockIn
    rcases blockIn with equal | inTail
    · subst head
      simp only [Std.HashSet.contains_insert, beq_self_eq_true, Bool.true_or,
        ↓reduceIte, notSeen]
      have blockNotTail := nodup.1
      have unchanged : ∀ other ∈ tail,
          (seen.insert block).contains other = seen.contains other := by
        intro other otherMem
        rw [Std.HashSet.contains_insert]
        have different : block ≠ other := by
          intro equal
          subst other
          exact blockNotTail otherMem
        simp [different]
      have tailsEqual :
          (tail.map fun current =>
            if (seen.insert block).contains current then
              0
            else
              dfsBlockWork irCtx current) =
          (tail.map fun current =>
            if seen.contains current then 0 else dfsBlockWork irCtx current) := by
        apply List.map_congr_left
        intro other otherMem
        rw [unchanged other otherMem]
      simp only [Std.HashSet.contains_insert] at tailsEqual
      rw [tailsEqual]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      omega
    · simp only [Std.HashSet.contains_insert]
      have different : block ≠ head := by
        intro equal
        subst head
        exact nodup.1 inTail
      have beqFalse : (block == head) = false := by
        simpa [beq_eq_false_iff_ne]
      simp only [beqFalse, Bool.false_or]
      simp only [Std.HashSet.contains_insert] at ih
      rw [Nat.add_assoc, ih nodup.2 inTail]

theorem dfsMeasure_push_lt
    (irCtx : WfIRContext OpCode)
    (seen : Std.HashSet BlockPtr)
    (stack : List (BlockPtr × Nat))
    (block successor : BlockPtr)
    (successorIndex : Nat)
    (successorInBounds : successor ∈ irCtx.raw.blocks.keys)
    (successorNotSeen : seen.contains successor = false)
    (successorIndexInBounds :
      successorIndex < (block.getSuccessors! irCtx.raw).size) :
    dfsMeasure irCtx (seen.insert successor)
        ((successor, 0) :: (block, successorIndex + 1) :: stack) <
      dfsMeasure irCtx seen ((block, successorIndex) :: stack) := by
  have unseen := dfsUnseenWork_insert irCtx seen successor
    successorInBounds successorNotSeen
  unfold dfsMeasure dfsStackWork at ⊢
  unfold dfsBlockWork at unseen
  simp only [List.map_cons, List.sum_cons]
  omega

theorem dfsMeasure_advance_lt
    (irCtx : WfIRContext OpCode)
    (seen : Std.HashSet BlockPtr)
    (stack : List (BlockPtr × Nat))
    (block : BlockPtr)
    (successorIndex : Nat)
    (successorIndexInBounds :
      successorIndex < (block.getSuccessors! irCtx.raw).size) :
    dfsMeasure irCtx seen ((block, successorIndex + 1) :: stack) <
      dfsMeasure irCtx seen ((block, successorIndex) :: stack) := by
  unfold dfsMeasure dfsStackWork
  simp only [List.map_cons, List.sum_cons]
  have remainingPositive : 0 < (block.getSuccessors! irCtx.raw).size - successorIndex := by
    omega
  have nextRemaining :
      (block.getSuccessors! irCtx.raw).size - (successorIndex + 1) =
        (block.getSuccessors! irCtx.raw).size - successorIndex - 1 := by
    omega
  rw [nextRemaining]
  omega

theorem dfsMeasure_pop_lt
    (irCtx : WfIRContext OpCode)
    (seen : Std.HashSet BlockPtr)
    (stack : List (BlockPtr × Nat))
    (block : BlockPtr)
    (successorIndex : Nat)
    (successorsDone : (block.getSuccessors! irCtx.raw).size ≤ successorIndex) :
    dfsMeasure irCtx seen stack <
      dfsMeasure irCtx seen ((block, successorIndex) :: stack) := by
  unfold dfsMeasure dfsStackWork
  simp only [List.map_cons, List.sum_cons]
  rw [Nat.sub_eq_zero_of_le successorsDone]
  omega

open Std.Do in
set_option mvcgen.warning false in
set_option linter.deprecated.syntax false in
/-- The concrete DFS returns a unique postorder rooted at the region entry. -/
theorem collectPostOrder_final
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (root : OperationPtr)
    (ctxVerified : irCtx.Verified root)
    (regionInBounds : region.InBounds irCtx.raw)
    (entry : BlockPtr)
    (entryEq : (region.get! irCtx.raw).firstBlock = some entry) :
    let postOrder := DominanceAnalysis.collectPostOrder region irCtx
    postOrder.toList.Nodup ∧
      postOrder.toList.getLast? = some entry ∧
      (∀ block, block ∈ postOrder →
        block.InBounds irCtx.raw ∧ (block.get! irCtx.raw).parent = some region) ∧
      (∀ block ∈ postOrder, ∀ successor ∈ block.getSuccessors! irCtx.raw,
        successor ∈ postOrder) ∧
      DFSCompletedHavePredecessor entry postOrder [] irCtx := by
  generalize resultEq : DominanceAnalysis.collectPostOrder region irCtx = result
  apply Id.of_wp_run_eq resultEq
  simp only [entryEq, WP.bind, SPred.entails_nil, SPred.down_pure, forall_const]
  mvcgen invariants
  | inv1 =>
      fun state => ⟨dfsMeasure irCtx state.2.2 state.2.1⟩
  | inv2 =>
      ⟨fun sum => match sum with
        | Sum.inl st =>
            ⌜DFSCollectorInvariant entry region irCtx
              st.1 st.2.1 st.2.2⌝
        | Sum.inr st => ⌜st.1.toList.Nodup ∧
            st.1.toList.getLast? = some entry ∧
            (∀ block, block ∈ st.1 → block.InBounds irCtx.raw ∧
              (block.get! irCtx.raw).parent = some region) ∧
            (∀ block ∈ st.1, ∀ successor ∈ block.getSuccessors! irCtx.raw,
              successor ∈ st.1) ∧
            DFSCompletedHavePredecessor entry st.1 [] irCtx⌝,
        ExceptConds.false⟩
  all_goals mleave
  · next state measure stackNotEmpty successorInBounds successorNotSeen stateFacts =>
    rcases stateFacts with ⟨variantEq, invariant⟩
    rcases state with ⟨postOrder, stack, seen⟩
    cases stack with
    | nil => simp at stackNotEmpty
    | cons frame stack =>
      rcases frame with ⟨block, successorIndex⟩
      simp [List.head!] at stackNotEmpty successorInBounds successorNotSeen ⊢
      have variantEq' : measure = dfsMeasure irCtx seen
          ((block, successorIndex) :: stack) := by
        simpa [WhileVariant.eval, SVal.evalsTo, SVal.curry, SVal.uncurry] using
          variantEq
      constructor
      · rw [variantEq']
        apply dfsMeasure_push_lt
        · rw [Std.HashMap.mem_keys]
          have blockValid := invariant.blocks_valid block (by
            simp [dfsCollectorBlocks, dfsStackBlocks])
          have successorMem :
              (block.getSuccessors! irCtx.raw)[successorIndex] ∈
                block.getSuccessors! irCtx.raw := Array.getElem_mem _
          exact BlockPtr.successor_inBounds irCtx blockValid.1 successorMem
        · simpa using successorNotSeen
        · exact successorInBounds
      · apply invariant.push ctxVerified successorInBounds
        · simpa using successorNotSeen
        · rfl
  · next state measure stackNotEmpty successorInBounds successorSeen stateFacts =>
    rcases stateFacts with ⟨variantEq, invariant⟩
    rcases state with ⟨postOrder, stack, seen⟩
    cases stack with
    | nil => simp at stackNotEmpty
    | cons frame stack =>
      rcases frame with ⟨block, successorIndex⟩
      simp [List.head!] at stackNotEmpty successorInBounds successorSeen ⊢
      have variantEq' : measure = dfsMeasure irCtx seen
          ((block, successorIndex) :: stack) := by
        simpa [WhileVariant.eval, SVal.evalsTo, SVal.curry, SVal.uncurry] using
          variantEq
      constructor
      · rw [variantEq']
        exact dfsMeasure_advance_lt irCtx seen stack block successorIndex
          successorInBounds
      · have successorSeen' :
            seen.contains (block.getSuccessors! irCtx.raw)[successorIndex]! = true := by
          rw [getElem!_pos (block.getSuccessors! irCtx.raw) successorIndex
            successorInBounds]
          change seen.contains
            (block.getSuccessors! irCtx.raw)[successorIndex] = true at successorSeen
          exact successorSeen
        exact invariant.advance successorInBounds successorSeen'
  · next state measure stackNotEmpty successorsDone stateFacts =>
    rcases stateFacts with ⟨variantEq, invariant⟩
    rcases state with ⟨postOrder, stack, seen⟩
    cases stack with
    | nil => simp at stackNotEmpty
    | cons frame stack =>
      rcases frame with ⟨block, successorIndex⟩
      simp [List.head!] at stackNotEmpty successorsDone ⊢
      have variantEq' : measure = dfsMeasure irCtx seen
          ((block, successorIndex) :: stack) := by
        simpa [WhileVariant.eval, SVal.evalsTo, SVal.curry, SVal.uncurry] using
          variantEq
      constructor
      · rw [variantEq']
        apply dfsMeasure_pop_lt
        omega
      · exact invariant.pop (by omega)
  · next state measure stackEmpty stateFacts =>
    rcases stateFacts with ⟨_, invariant⟩
    rcases state with ⟨postOrder, stack, seen⟩
    have stackIsEmpty : stack = [] := by
      simpa using stackEmpty
    subst stack
    exact ⟨by simpa [dfsCollectorBlocks, dfsStackBlocks] using
        invariant.blocks_nodup,
      by simpa [dfsCollectorBlocks, dfsStackBlocks] using invariant.entry_last,
      fun block blockMem => invariant.blocks_valid block (by
        simpa [dfsCollectorBlocks, dfsStackBlocks] using blockMem),
      fun block blockMem successor successorMem => by
        have successorSeen := invariant.completed_successors_seen
          block blockMem successor successorMem
        have successorCollected := (invariant.seen_iff successor).1 successorSeen
        simpa [dfsCollectorBlocks, dfsStackBlocks] using successorCollected,
      invariant.completed_have_predecessor⟩
  · exact DFSCollectorInvariant.init region irCtx regionInBounds entry entryEq
  · intros nodup entryLast blocksValid successors predecessors
    exact ⟨nodup, entryLast, blocksValid, successors, predecessors⟩

/-- Successor closure carries membership from a path's source to its target. -/
theorem RegionPtr.Path.target_mem_of_successor_closed
    {region : RegionPtr}
    {irCtx : WfIRContext OpCode}
    {source target : BlockPtr}
    {blocks : List BlockPtr}
    {collected : Array BlockPtr}
    (path : region.Path irCtx source target blocks)
    (sourceMem : source ∈ collected)
    (successorClosed : ∀ block ∈ collected,
      ∀ successor ∈ block.getSuccessors! irCtx.raw, successor ∈ collected) :
    target ∈ collected := by
  induction path with
  | Single => exact sourceMem
  | @Cons source next target blocks parent successor tail ih =>
      exact ih (successorClosed source sourceMem next successor)

/-- The concrete DFS reverse postorder represents every block reachable from the entry. -/
theorem collectPostOrder_reverse_reachable
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (root : OperationPtr)
    (ctxVerified : irCtx.Verified root)
    (regionInBounds : region.InBounds irCtx.raw)
    (entry : BlockPtr)
    (entryEq : (region.get! irCtx.raw).firstBlock = some entry) :
    let reversePostOrder :=
      (DominanceAnalysis.collectPostOrder region irCtx).reverse
    ReachableBlocksRepresented (reversePostOrderVector reversePostOrder) region irCtx := by
  let postOrder := DominanceAnalysis.collectPostOrder region irCtx
  let reversePostOrder := postOrder.reverse
  obtain ⟨_, entryLast, _, successorClosed, _⟩ :=
    collectPostOrder_final region irCtx root ctxVerified regionInBounds entry entryEq
  unfold ReachableBlocksRepresented
  dsimp only
  intro block reachable
  obtain ⟨pathEntry, blocks, pathEntryEq, path⟩ := reachable.exists_path
  have pathEntryIsEntry : pathEntry = entry := by
    rw [entryEq] at pathEntryEq
    exact Option.some.inj pathEntryEq |>.symm
  subst pathEntry
  have entryMem : entry ∈ postOrder := by
    obtain ⟨beforeEntry, postOrderEq⟩ := List.getLast?_eq_some_iff.mp entryLast
    rw [← Array.mem_toList_iff, postOrderEq]
    simp
  have blockMem : block ∈ postOrder :=
    DominanceValue.RegionPtr.Path.target_mem_of_successor_closed
      path entryMem successorClosed
  have reverseMem : block ∈ reversePostOrder := by
    rw [← Array.mem_toList_iff, Array.toList_reverse]
    simpa only [List.mem_reverse, Array.mem_toList_iff] using blockMem
  obtain ⟨blockIndex, blockIndexInBounds, blockEq⟩ :=
    Array.mem_iff_getElem.mp reverseMem
  let blockIndexFin : Fin reversePostOrder.size := ⟨blockIndex, blockIndexInBounds⟩
  refine ⟨blockIndexFin, ?_⟩
  simpa only [reversePostOrderVector_get, blockIndexFin] using blockEq

/-- Reversing the concrete DFS postorder establishes the CHK ordering contract. -/
theorem collectPostOrder_reverse_forRegion
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (root : OperationPtr)
    (ctxVerified : irCtx.Verified root)
    (regionInBounds : region.InBounds irCtx.raw)
    (entry : BlockPtr)
    (entryEq : (region.get! irCtx.raw).firstBlock = some entry) :
    let reversePostOrder :=
      (DominanceAnalysis.collectPostOrder region irCtx).reverse
    ∃ nonempty : reversePostOrder.size ≠ 0,
      @ReversePostOrderForRegion reversePostOrder ⟨nonempty⟩ region irCtx := by
  let postOrder := DominanceAnalysis.collectPostOrder region irCtx
  let reversePostOrder := postOrder.reverse
  obtain ⟨postNodup, entryLast, blocksValid, _, completed⟩ :=
    collectPostOrder_final region irCtx root ctxVerified regionInBounds entry entryEq
  change postOrder.toList.Nodup at postNodup
  change postOrder.toList.getLast? = some entry at entryLast
  change (∀ block, block ∈ postOrder →
    block.InBounds irCtx.raw ∧ (block.get! irCtx.raw).parent = some region) at blocksValid
  change DFSCompletedHavePredecessor entry postOrder [] irCtx at completed
  obtain ⟨beforeEntry, postEq⟩ := List.getLast?_eq_some_iff.mp entryLast
  have reverseListEq : reversePostOrder.toList = entry :: beforeEntry.reverse := by
    simp [reversePostOrder, Array.toList_reverse, postEq]
  have nonempty : reversePostOrder.size ≠ 0 := by
    have positive : 0 < reversePostOrder.toList.length := by
      rw [reverseListEq]
      simp
    simpa using Nat.ne_of_gt positive
  letI nonzero : NeZero reversePostOrder.size := ⟨nonempty⟩
  have reverseNodup : reversePostOrder.toList.Nodup :=
    array_reverse_toList_nodup postOrder postNodup
  have reverseInjective : Function.Injective
      (fun index : Fin reversePostOrder.size => reversePostOrder[index.val]) :=
    array_get_injective_of_toList_nodup reversePostOrder reverseNodup
  have zeroInList : 0 < reversePostOrder.toList.length := by
    rw [reverseListEq]
    simp
  have zeroInArray : 0 < reversePostOrder.size := by
    simpa using zeroInList
  have entryFirst : reversePostOrder[0]'zeroInArray = entry := by
    have firstOption := congrArg (fun blocks => blocks[0]?) reverseListEq
    have firstOptionEq : reversePostOrder.toList[0]? = some entry := by
      simpa using firstOption
    rw [List.getElem?_eq_getElem zeroInList] at firstOptionEq
    have firstList : reversePostOrder.toList[0]'zeroInList = entry :=
      Option.some.inj firstOptionEq
    simpa only [Array.getElem_toList] using firstList
  refine ⟨nonempty, @ReversePostOrderForRegion.mk reversePostOrder nonzero region irCtx
    ?_ ?_ reverseInjective ?_⟩
  · rw [getElem!_pos reversePostOrder 0 (Nat.pos_of_neZero _), entryFirst]
    exact entryEq
  · intro blockIndex
    apply (blocksValid reversePostOrder[blockIndex.val] ?_).2
    have reverseMem : reversePostOrder[blockIndex.val] ∈ reversePostOrder :=
      Array.getElem_mem _
    simp [reversePostOrder, postOrder] at reverseMem ⊢
  · intro blockIndex blockNotFirst
    have blockMem : reversePostOrder[blockIndex.val] ∈ postOrder := by
      have reverseMem : reversePostOrder[blockIndex.val] ∈ reversePostOrder :=
        Array.getElem_mem _
      simp [reversePostOrder] at reverseMem ⊢
    have blockNotEntry : reversePostOrder[blockIndex.val] ≠ entry := by
      intro blockIsEntry
      let entryIndex : Fin reversePostOrder.size :=
        ⟨0, Nat.pos_of_neZero reversePostOrder.size⟩
      have indicesEqual : blockIndex = entryIndex := by
        apply reverseInjective
        simpa [entryIndex, entryFirst] using blockIsEntry
      exact blockNotFirst (congrArg Fin.val indicesEqual)
    obtain ⟨predecessor, edge, onStack | before⟩ :=
      completed reversePostOrder[blockIndex.val] blockMem blockNotEntry
    · simp [dfsStackBlocks] at onStack
    · have reverseBefore :
          List.Before predecessor reversePostOrder[blockIndex.val]
            reversePostOrder.toList := by
        simpa [reversePostOrder, postOrder, Array.toList_reverse] using before.reverse
      obtain ⟨predecessorIndex, representedBlockIndex,
          predecessorInBounds, representedBlockInBounds, earlier,
          predecessorEq, representedBlockEq⟩ := reverseBefore.exists_indices
      let predecessorFin : Fin reversePostOrder.size := by
        refine ⟨predecessorIndex, ?_⟩
        simpa using predecessorInBounds
      have representedIndexEq : representedBlockIndex = blockIndex.val := by
        apply reverseNodup.eq_of_getElem_eq
          (by simpa using representedBlockInBounds) (by simpa using blockIndex.isLt)
        rw [Array.getElem_toList, Array.getElem_toList]
        exact representedBlockEq
      refine ⟨predecessorFin, ?_, ?_⟩
      · change predecessorIndex < blockIndex.val
        omega
      · have predecessorBlockEq :
            reversePostOrder[predecessorFin.val] = predecessor := by
          rw [← Array.getElem_toList]
          exact predecessorEq
        rw [predecessorBlockEq]
        exact edge

/--
The fixed region metadata needed by the CHK correctness proof. These are the
properties that `collectPostOrder`, the dense index map, and
`collectPredecessors` must establish.
-/
structure RegionMetadataForRegion [HasOpInfo OpInfo] [NeZero blockCount]
    (reversePostOrder : Vector BlockPtr blockCount)
    (predecessors : Array (Array Nat))
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo) : Prop where
  entry_is_first : (region.get! irCtx.raw).firstBlock =
    some (reversePostOrder.get ⟨0, Nat.pos_of_neZero blockCount⟩)
  predecessors_size : predecessors.size = blockCount
  blocks_parent : ∀ blockIndex : Fin blockCount,
    ((reversePostOrder.get blockIndex).get! irCtx.raw).parent = some region
  injective_rpo : InjectiveRPO reversePostOrder
  predecessors_sound : ∀ (blockIndex : Fin blockCount) predecessorIndex,
    predecessorIndex ∈ predecessors[blockIndex.val]! →
    PredecessorIndexForBlock reversePostOrder region irCtx
      blockIndex predecessorIndex
  earlier_predecessor : ∀ blockIndex : Fin blockCount,
    blockIndex.val ≠ 0 →
    ∃ predecessorIndex : Fin blockCount,
      predecessorIndex < blockIndex ∧
      predecessorIndex.val ∈ predecessors[blockIndex.val]!

/-- Every CFG edge between represented blocks occurs in the cached predecessor table. -/
def PredecessorTableCompleteForRegion [HasOpInfo OpInfo]
    (reversePostOrder : Vector BlockPtr blockCount)
    (predecessors : Array (Array Nat))
    (irCtx : WfIRContext OpInfo) : Prop :=
  ∀ (blockIndex predecessorIndex : Fin blockCount),
    reversePostOrder.get blockIndex ∈
      (reversePostOrder.get predecessorIndex).getSuccessors! irCtx.raw →
    predecessorIndex.val ∈ predecessors[blockIndex.val]!

/-- View the metadata's cached RPO array at its statically known size. -/
def regionDominanceReversePostOrder
    (metadata : RegionDominanceMetadata) :
    Vector BlockPtr metadata.reversePostOrder.size :=
  ⟨metadata.reversePostOrder, rfl⟩

@[simp]
theorem regionDominanceReversePostOrder_get
    (metadata : RegionDominanceMetadata)
    (index : Fin metadata.reversePostOrder.size) :
    (regionDominanceReversePostOrder metadata).get index =
      metadata.reversePostOrder[index.val] := by
  unfold regionDominanceReversePostOrder Vector.get
  apply getElem_congr_idx
  rfl

/-- Correctness of the concrete fixed metadata stored in a dominance fact. -/
def RegionDominanceMetadataCorrectForRegion [HasOpInfo OpInfo]
    (metadata : RegionDominanceMetadata)
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo)
    [NeZero metadata.reversePostOrder.size] : Prop :=
  RegionMetadataForRegion (regionDominanceReversePostOrder metadata)
    metadata.predecessors region irCtx

/-- A nonempty metadata value together with its semantic region contract. -/
def RegionDominanceMetadataCertifiedForRegion
    (metadata : RegionDominanceMetadata)
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode) : Prop :=
  ∃ h : metadata.reversePostOrder.size ≠ 0,
    @RegionDominanceMetadataCorrectForRegion OpCode inferInstance metadata region irCtx ⟨h⟩

open Std.Do in
set_option mvcgen.warning false in
set_option linter.deprecated.syntax false in
/-- `buildBlockIndex` is a left inverse of an injective RPO array. -/
theorem buildBlockIndex_get?_of_injective
    (reversePostOrder : Array BlockPtr)
    (injective : Function.Injective fun index : Fin reversePostOrder.size =>
      reversePostOrder[index.val])
    (index : Fin reversePostOrder.size) :
    (DominanceAnalysis.buildBlockIndex reversePostOrder).get?
      reversePostOrder[index.val] = some index.val := by
  generalize resultEq : DominanceAnalysis.buildBlockIndex reversePostOrder = result
  apply Id.of_wp_run_eq resultEq
  simp only [WP.bind, SPred.entails_nil, SPred.down_pure, forall_const]
  mvcgen invariants
  | inv1 =>
      ⟨fun ⟨cursor, blockIndex⟩ => ⌜∀ i : Fin reversePostOrder.size,
          i.val < cursor.prefix.length →
            blockIndex.get? reversePostOrder[i.val] = some i.val⌝,
        ExceptConds.false⟩
  all_goals mleave
  · next pref current suffix splitRange blockIndex inductionHypothesis =>
    simp only [Std.Legacy.Range.toList, Nat.sub_zero, Nat.div_one] at splitRange
    have countEq : reversePostOrder.size + 1 - 1 = reversePostOrder.size := by
      omega
    rw [countEq] at splitRange
    have prefixLength : pref.length < reversePostOrder.size := by
      have lengths := congrArg List.length splitRange
      simp only [List.length_range', List.length_append, List.length_cons] at lengths
      omega
    have currentEq : current = pref.length := by
      have currentAtPrefix := congrArg (fun list => list[pref.length]?) splitRange
      rw [List.getElem?_range' prefixLength] at currentAtPrefix
      simp only [Nat.zero_add, Nat.one_mul,
        List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at currentAtPrefix
      simpa using currentAtPrefix.symm
    have currentInBounds : current < reversePostOrder.size := by
      omega
    intro i hi
    rw [Std.HashMap.get?_insert]
    split
    · rename_i sameBlock
      have sameIndex : i.val = current := by
        let currentIndex : Fin reversePostOrder.size := ⟨current, currentInBounds⟩
        have indicesEqual : i = currentIndex := by
          apply injective
          exact beq_iff_eq.mp sameBlock |>.symm
        exact congrArg Fin.val indicesEqual
      simp only [sameIndex]
    · rename_i differentBlock
      apply inductionHypothesis i
      simp only [List.length_append, List.length_singleton] at hi
      have differentIndex : i.val ≠ current := by
        intro sameIndex
        apply differentBlock
        apply beq_iff_eq.mpr
        simp only [sameIndex]
      rw [currentEq] at differentIndex
      omega
  · simp
  · intro allIndices
    apply allIndices index
    simp

open Std.Do in
set_option mvcgen.warning false in
set_option linter.deprecated.syntax false in
/-- Every successful inverse-map lookup points back to the queried RPO block. -/
theorem buildBlockIndex_get?_sound
    (reversePostOrder : Array BlockPtr) :
    ∀ block index,
      (DominanceAnalysis.buildBlockIndex reversePostOrder).get? block = some index →
      ∃ representedIndex : Fin reversePostOrder.size,
        representedIndex.val = index ∧ reversePostOrder[representedIndex.val] = block := by
  generalize resultEq : DominanceAnalysis.buildBlockIndex reversePostOrder = result
  apply Id.of_wp_run_eq resultEq
  simp only [WP.bind, SPred.entails_nil, SPred.down_pure, forall_const]
  mvcgen invariants
  | inv1 =>
      ⟨fun ⟨_, blockIndex⟩ => ⌜∀ block index,
          blockIndex.get? block = some index →
            ∃ representedIndex : Fin reversePostOrder.size,
              representedIndex.val = index ∧
                reversePostOrder[representedIndex.val] = block⌝,
        ExceptConds.false⟩
  all_goals mleave
  · next pref current suffix split blockIndex invariant =>
    intro queriedBlock queriedIndex queriedLookup
    rw [Std.HashMap.get?_insert] at queriedLookup
    split at queriedLookup
    · rename_i sameBlock
      have currentInBounds : current < reversePostOrder.size := by
        have currentMem : current ∈ [:reversePostOrder.size].toList := by
          rw [split]
          simp
        simpa [Std.Legacy.Range.toList] using currentMem
      refine ⟨⟨current, currentInBounds⟩, ?_, ?_⟩
      · exact Option.some.inj queriedLookup
      · exact beq_iff_eq.mp sameBlock
    · exact invariant queriedBlock queriedIndex queriedLookup
  · intro block index lookup
    simp at lookup
  · intro invariant
    exact invariant

open Std.Do in
set_option mvcgen.warning false in
set_option linter.deprecated.syntax false in
/-- Adding successor edges does not change the number of predecessor rows. -/
theorem addPredecessorEdges_size
    (predecessors : Array (Array Nat))
    (predecessorIndex : Nat)
    (successors : Array BlockPtr)
    (blockIndex : Std.HashMap BlockPtr Nat) :
    (DominanceAnalysis.addPredecessorEdges predecessors predecessorIndex successors
      blockIndex).size = predecessors.size := by
  generalize resultEq :
    DominanceAnalysis.addPredecessorEdges predecessors predecessorIndex successors blockIndex =
      result
  apply Id.of_wp_run_eq resultEq
  simp only [WP.bind, SPred.entails_nil, SPred.down_pure, forall_const]
  mvcgen invariants
  | inv1 =>
      ⟨fun ⟨_, current⟩ => ⌜current.size = predecessors.size⌝,
        ExceptConds.false⟩
  all_goals mleave
  all_goals try simp_all
  intro invariant
  exact invariant

open Std.Do in
set_option mvcgen.warning false in
set_option linter.deprecated.syntax false in
/-- `collectPredecessors` allocates exactly one predecessor row per RPO block. -/
theorem collectPredecessors_size
    (reversePostOrder : Array BlockPtr)
    (blockIndex : Std.HashMap BlockPtr Nat)
    (irCtx : WfIRContext OpCode) :
    (DominanceAnalysis.collectPredecessors reversePostOrder blockIndex irCtx).size =
      reversePostOrder.size := by
  generalize resultEq :
    DominanceAnalysis.collectPredecessors reversePostOrder blockIndex irCtx = result
  apply Id.of_wp_run_eq resultEq
  simp only [WP.bind, SPred.entails_nil, SPred.down_pure, forall_const]
  mvcgen invariants
  | inv1 =>
      ⟨fun ⟨_, predecessors⟩ => ⌜predecessors.size = reversePostOrder.size⌝,
        ExceptConds.false⟩
  all_goals mleave
  · next pref current suffix split table invariant =>
    rw [addPredecessorEdges_size]
    exact invariant
  · simp
  · intro invariant
    exact invariant

/-- Every cached index in a predecessor table was inserted from a represented edge. -/
def PredecessorTableSound
    (reversePostOrder : Array BlockPtr)
    (blockIndex : Std.HashMap BlockPtr Nat)
    (irCtx : WfIRContext OpCode)
    (predecessors : Array (Array Nat)) : Prop :=
  predecessors.size = reversePostOrder.size ∧
    ∀ (targetIndex : Fin reversePostOrder.size) predecessorIndex,
      predecessorIndex ∈ predecessors[targetIndex.val]! →
      ∃ predecessor : Fin reversePostOrder.size,
        predecessor.val = predecessorIndex ∧
        ∃ block, block ∈ reversePostOrder[predecessor.val].getSuccessors! irCtx.raw ∧
          blockIndex.get? block = some targetIndex.val

open Std.Do in
set_option mvcgen.warning false in
set_option linter.deprecated.syntax false in
/-- Adding one source block's edges preserves predecessor-table soundness. -/
theorem addPredecessorEdges_sound
    (reversePostOrder : Array BlockPtr)
    (blockIndex : Std.HashMap BlockPtr Nat)
    (irCtx : WfIRContext OpCode)
    (predecessors : Array (Array Nat))
    (predecessorIndex : Fin reversePostOrder.size)
    (sound : PredecessorTableSound reversePostOrder blockIndex irCtx predecessors) :
    PredecessorTableSound reversePostOrder blockIndex irCtx
      (DominanceAnalysis.addPredecessorEdges predecessors predecessorIndex.val
        (reversePostOrder[predecessorIndex.val].getSuccessors! irCtx.raw) blockIndex) := by
  generalize resultEq :
    DominanceAnalysis.addPredecessorEdges predecessors predecessorIndex.val
      (reversePostOrder[predecessorIndex.val].getSuccessors! irCtx.raw) blockIndex = result
  apply Id.of_wp_run_eq resultEq
  simp only [WP.bind, SPred.entails_nil, SPred.down_pure, forall_const]
  mvcgen invariants
  | inv1 =>
      ⟨fun ⟨_, current⟩ =>
          ⌜PredecessorTableSound reversePostOrder blockIndex irCtx current⌝,
        ExceptConds.false⟩
  all_goals mleave
  · next successorPrefix block successorSuffix successorSplit current index lookup invariant =>
    constructor
    · simpa [PredecessorTableSound] using invariant.1
    · intro targetIndex source sourceMem
      have targetInBounds : targetIndex.val <
          (current.modify index fun indices => indices.push predecessorIndex.val).size := by
        rw [Array.size_modify, invariant.1]
        exact targetIndex.isLt
      rw [getElem!_pos
        (current.modify index fun indices => indices.push predecessorIndex.val)
        targetIndex.val targetInBounds] at sourceMem
      rw [Array.getElem_modify] at sourceMem
      split at sourceMem
      · rename_i modifiedTarget
        rw [Array.mem_push] at sourceMem
        rcases sourceMem with oldSource | newSource
        · apply invariant.2 targetIndex source
          rw [getElem!_pos current targetIndex.val (by
            rw [invariant.1]
            exact targetIndex.isLt)]
          exact oldSource
        · subst source
          refine ⟨predecessorIndex, rfl, block, ?_, ?_⟩
          · rw [← Array.mem_toList_iff, successorSplit]
            simp
          · have targetEq : index = targetIndex.val := modifiedTarget
            simpa only [targetEq] using lookup
      · apply invariant.2 targetIndex source
        rw [getElem!_pos current targetIndex.val (by
          rw [invariant.1]
          exact targetIndex.isLt)]
        exact sourceMem
  all_goals try assumption
  intro invariant
  exact invariant

open Std.Do in
set_option mvcgen.warning false in
set_option linter.deprecated.syntax false in
/-- Adding edges never removes an existing cached predecessor. -/
theorem addPredecessorEdges_preserves
    (predecessors : Array (Array Nat))
    (predecessorIndex : Nat)
    (successors : Array BlockPtr)
    (blockIndex : Std.HashMap BlockPtr Nat)
    (targetIndex : Fin predecessors.size)
    (sourceIndex : Nat)
    (sourceMem : sourceIndex ∈ predecessors[targetIndex.val]!) :
    sourceIndex ∈
      (DominanceAnalysis.addPredecessorEdges predecessors predecessorIndex successors
        blockIndex)[targetIndex.val]! := by
  generalize resultEq :
    DominanceAnalysis.addPredecessorEdges predecessors predecessorIndex successors blockIndex =
      result
  apply Id.of_wp_run_eq resultEq
  simp only [WP.bind, SPred.entails_nil, SPred.down_pure, forall_const]
  mvcgen invariants
  | inv1 =>
      ⟨fun ⟨_, current⟩ =>
          ⌜current.size = predecessors.size ∧
            sourceIndex ∈ current[targetIndex.val]!⌝,
        ExceptConds.false⟩
  all_goals mleave
  · next successorPrefix block successorSuffix successorSplit current index lookup invariant =>
    constructor
    · simpa using invariant.1
    · have targetInBounds : targetIndex.val < current.size := by
        rw [invariant.1]
        exact targetIndex.isLt
      rw [getElem!_pos
        (current.modify index fun indices => indices.push predecessorIndex)
        targetIndex.val (by simpa using targetInBounds)]
      rw [Array.getElem_modify]
      split
      · rw [Array.mem_push]
        exact Or.inl (by
          rw [← getElem!_pos current targetIndex.val targetInBounds]
          exact invariant.2)
      · rw [← getElem!_pos current targetIndex.val targetInBounds]
        exact invariant.2
  all_goals try assumption
  · intro _ invariant
    exact invariant

open Std.Do in
set_option mvcgen.warning false in
set_option linter.deprecated.syntax false in
/-- Every supplied successor edge is inserted into its indexed predecessor row. -/
theorem addPredecessorEdges_complete
    (predecessors : Array (Array Nat))
    (predecessorIndex : Nat)
    (successors : Array BlockPtr)
    (blockIndex : Std.HashMap BlockPtr Nat)
    (targetIndex : Fin predecessors.size)
    (target : BlockPtr)
    (edge : target ∈ successors)
    (lookup : blockIndex.get? target = some targetIndex.val) :
    predecessorIndex ∈
      (DominanceAnalysis.addPredecessorEdges predecessors predecessorIndex successors
        blockIndex)[targetIndex.val]! := by
  generalize resultEq :
    DominanceAnalysis.addPredecessorEdges predecessors predecessorIndex successors blockIndex =
      result
  apply Id.of_wp_run_eq resultEq
  simp only [WP.bind, SPred.entails_nil, SPred.down_pure, forall_const]
  mvcgen invariants
  | inv1 =>
      ⟨fun ⟨cursor, current⟩ =>
          ⌜current.size = predecessors.size ∧
            (target ∈ cursor.prefix → predecessorIndex ∈ current[targetIndex.val]!)⌝,
        ExceptConds.false⟩
  all_goals mleave
  · next successorPrefix block successorSuffix successorSplit current index blockLookup invariant =>
    constructor
    · simpa using invariant.1
    · intro targetMem
      simp only [List.mem_append, List.mem_singleton] at targetMem
      have targetInBounds : targetIndex.val < current.size := by
        rw [invariant.1]
        exact targetIndex.isLt
      rw [getElem!_pos
        (current.modify index fun indices => indices.push predecessorIndex)
        targetIndex.val (by simpa using targetInBounds)]
      rw [Array.getElem_modify]
      split
      · rw [Array.mem_push]
        rcases targetMem with oldTarget | currentTarget
        · exact Or.inl (by
            rw [← getElem!_pos current targetIndex.val targetInBounds]
            exact invariant.2 oldTarget)
        · exact Or.inr rfl
      · rename_i differentTarget
        rcases targetMem with oldTarget | currentTarget
        · rw [← getElem!_pos current targetIndex.val targetInBounds]
          exact invariant.2 oldTarget
        · subst block
          have : index = targetIndex.val := Option.some.inj (blockLookup.symm.trans lookup)
          exact False.elim (differentTarget this)
  · next successorPrefix block successorSuffix successorSplit current lookupResult
        notSome blockLookup invariant =>
    refine ⟨invariant.1, ?_⟩
    intro targetMem
    simp only [List.mem_append, List.mem_singleton] at targetMem
    rcases targetMem with oldTarget | currentTarget
    · exact invariant.2 oldTarget
    · subst block
      exact False.elim (notSome targetIndex (blockLookup.symm.trans lookup))
  · simp
  · intro _ invariant
    exact invariant (Array.mem_toList_iff.mpr edge)

open Std.Do in
set_option mvcgen.warning false in
set_option linter.deprecated.syntax false in
/-- Every cached predecessor produced by `collectPredecessors` denotes an input edge. -/
theorem collectPredecessors_sound
    (reversePostOrder : Array BlockPtr)
    (blockIndex : Std.HashMap BlockPtr Nat)
    (irCtx : WfIRContext OpCode) :
    PredecessorTableSound reversePostOrder blockIndex irCtx
      (DominanceAnalysis.collectPredecessors reversePostOrder blockIndex irCtx) := by
  generalize resultEq :
    DominanceAnalysis.collectPredecessors reversePostOrder blockIndex irCtx = result
  apply Id.of_wp_run_eq resultEq
  simp only [WP.bind, SPred.entails_nil, SPred.down_pure, forall_const]
  mvcgen invariants
  | inv1 =>
      ⟨fun ⟨_, predecessors⟩ =>
          ⌜PredecessorTableSound reversePostOrder blockIndex irCtx predecessors⌝,
        ExceptConds.false⟩
  all_goals mleave
  · next pref predecessorIndex suffix split predecessors invariant =>
    have predecessorInBounds : predecessorIndex < reversePostOrder.size := by
      have predecessorMem : predecessorIndex ∈ [:reversePostOrder.size].toList := by
        rw [split]
        simp
      simpa [Std.Legacy.Range.toList] using predecessorMem
    exact addPredecessorEdges_sound reversePostOrder blockIndex irCtx predecessors
      ⟨predecessorIndex, predecessorInBounds⟩ invariant
  · constructor
    · simp
    · intro targetIndex source sourceMem
      simp at sourceMem
  · intro invariant
    exact invariant

open Std.Do in
set_option mvcgen.warning false in
set_option linter.deprecated.syntax false in
/-- Every represented CFG edge is cached in its target's predecessor row. -/
theorem collectPredecessors_complete
    (reversePostOrder : Array BlockPtr)
    (blockIndex : Std.HashMap BlockPtr Nat)
    (irCtx : WfIRContext OpCode)
    (predecessorIndex targetIndex : Fin reversePostOrder.size)
    (edge : reversePostOrder[targetIndex.val] ∈
      reversePostOrder[predecessorIndex.val].getSuccessors! irCtx.raw)
    (lookup : blockIndex.get? reversePostOrder[targetIndex.val] = some targetIndex.val) :
    predecessorIndex.val ∈
      (DominanceAnalysis.collectPredecessors
        reversePostOrder blockIndex irCtx)[targetIndex.val]! := by
  generalize resultEq :
    DominanceAnalysis.collectPredecessors reversePostOrder blockIndex irCtx = result
  apply Id.of_wp_run_eq resultEq
  simp only [WP.bind, SPred.entails_nil, SPred.down_pure, forall_const]
  mvcgen invariants
  | inv1 =>
      ⟨fun ⟨cursor, predecessors⟩ =>
          ⌜predecessors.size = reversePostOrder.size ∧
            (predecessorIndex.val ∈ cursor.prefix →
              predecessorIndex.val ∈ predecessors[targetIndex.val]!)⌝,
        ExceptConds.false⟩
  all_goals mleave
  · next pref currentIndex suffix split predecessors invariant =>
    constructor
    · simpa [addPredecessorEdges_size] using invariant.1
    · intro predecessorMem
      simp only [List.mem_append, List.mem_singleton] at predecessorMem
      have targetInBounds : targetIndex.val < predecessors.size := by
        rw [invariant.1]
        exact targetIndex.isLt
      have currentInBounds : currentIndex < reversePostOrder.size := by
        have currentMem : currentIndex ∈ [:reversePostOrder.size].toList := by
          rw [split]
          simp
        simpa [Std.Legacy.Range.toList] using currentMem
      let currentTarget : Fin predecessors.size := ⟨targetIndex.val, targetInBounds⟩
      rcases predecessorMem with oldPredecessor | currentPredecessor
      · apply addPredecessorEdges_preserves predecessors currentIndex
          (reversePostOrder[currentIndex].getSuccessors! irCtx.raw) blockIndex
          currentTarget predecessorIndex.val
        simpa only [currentTarget] using invariant.2 oldPredecessor
      · subst currentIndex
        apply addPredecessorEdges_complete predecessors predecessorIndex.val
          (reversePostOrder[predecessorIndex.val].getSuccessors! irCtx.raw)
          blockIndex currentTarget reversePostOrder[targetIndex.val] edge
        simpa only [currentTarget] using lookup
  · simp
  · intro _ invariant
    apply invariant
    simp [Std.Legacy.Range.toList, predecessorIndex.isLt]

/-- The fixed metadata collectors satisfy the solver contract for any lawful RPO. -/
theorem collectPredecessors_correct_of_rpo
    (reversePostOrder : Array BlockPtr)
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    [NeZero reversePostOrder.size]
    (rpoCorrect : ReversePostOrderForRegion reversePostOrder region irCtx) :
    RegionMetadataForRegion (reversePostOrderVector reversePostOrder)
      (DominanceAnalysis.collectPredecessors reversePostOrder
        (DominanceAnalysis.buildBlockIndex reversePostOrder) irCtx) region irCtx := by
  let blockIndex := DominanceAnalysis.buildBlockIndex reversePostOrder
  let predecessors := DominanceAnalysis.collectPredecessors reversePostOrder blockIndex irCtx
  have indexCorrect : ∀ index : Fin reversePostOrder.size,
      blockIndex.get? reversePostOrder[index.val] = some index.val := by
    exact buildBlockIndex_get?_of_injective reversePostOrder rpoCorrect.injective_rpo
  have tableSound : PredecessorTableSound reversePostOrder blockIndex irCtx predecessors := by
    exact collectPredecessors_sound reversePostOrder blockIndex irCtx
  constructor
  · have entry := rpoCorrect.entry_is_first
    rw [getElem!_pos reversePostOrder 0 (Nat.pos_of_neZero _)] at entry
    simpa only [reversePostOrderVector_get] using entry
  · exact collectPredecessors_size reversePostOrder blockIndex irCtx
  · intro blockIndexFin
    simpa only [reversePostOrderVector_get] using rpoCorrect.blocks_parent blockIndexFin
  · intro first second equalBlocks
    apply rpoCorrect.injective_rpo
    simpa only [reversePostOrderVector_get] using equalBlocks
  · intro targetIndex predecessorIndex predecessorMem
    have predecessorMem' : predecessorIndex ∈ predecessors[targetIndex.val]! := by
      simpa only [predecessors] using predecessorMem
    obtain ⟨predecessor, predecessorEq, block, edge, lookup⟩ :=
      tableSound.2 targetIndex predecessorIndex predecessorMem'
    obtain ⟨representedTarget, targetEq, blockEq⟩ :=
      buildBlockIndex_get?_sound reversePostOrder block targetIndex.val lookup
    have representedTargetEq : representedTarget = targetIndex := by
      exact Fin.eq_of_val_eq targetEq
    subst representedTarget
    refine ⟨predecessor, predecessorEq, ?_, ?_⟩
    · simpa only [reversePostOrderVector_get] using rpoCorrect.blocks_parent predecessor
    · simpa only [reversePostOrderVector_get, blockEq] using edge
  · intro targetIndex targetNotEntry
    obtain ⟨predecessorIndex, predecessorEarlier, edge⟩ :=
      rpoCorrect.earlier_predecessor targetIndex targetNotEntry
    refine ⟨predecessorIndex, predecessorEarlier, ?_⟩
    exact collectPredecessors_complete reversePostOrder blockIndex irCtx
      predecessorIndex targetIndex edge (indexCorrect targetIndex)

/-- The concrete predecessor collector caches every edge between represented blocks. -/
theorem collectPredecessors_complete_of_rpo
    (reversePostOrder : Array BlockPtr)
    (irCtx : WfIRContext OpCode)
    (injective : Function.Injective fun index : Fin reversePostOrder.size =>
      reversePostOrder[index.val]) :
    PredecessorTableCompleteForRegion (reversePostOrderVector reversePostOrder)
      (DominanceAnalysis.collectPredecessors reversePostOrder
        (DominanceAnalysis.buildBlockIndex reversePostOrder) irCtx) irCtx := by
  intro blockIndex predecessorIndex edge
  apply collectPredecessors_complete reversePostOrder
    (DominanceAnalysis.buildBlockIndex reversePostOrder) irCtx predecessorIndex blockIndex
  · simpa only [reversePostOrderVector_get] using edge
  · exact buildBlockIndex_get?_of_injective reversePostOrder injective blockIndex

/-- Every edge in the temporary validation index came from a represented successor array. -/
theorem collectEdges_sound
    (metadata : RegionDominanceMetadata)
    (irCtx : WfIRContext OpCode)
    (predecessor block : BlockPtr)
    (edge : (predecessor, block) ∈ DominanceAnalysis.collectEdges metadata irCtx) :
    block ∈ predecessor.getSuccessors! irCtx.raw := by
  unfold DominanceAnalysis.collectEdges at edge
  rw [Std.HashSet.mem_ofList, List.contains_iff_mem, List.mem_flatMap] at edge
  obtain ⟨representedPredecessor, _, pairMem⟩ := edge
  rw [List.mem_map] at pairMem
  obtain ⟨representedBlock, blockMem, pairEq⟩ := pairMem
  rw [Array.mem_toList_iff] at blockMem
  simp only [Prod.mk.injEq] at pairEq
  rw [pairEq.1, pairEq.2] at blockMem
  exact blockMem

/-- Every represented successor edge occurs in the temporary validation index. -/
theorem collectEdges_complete
    (metadata : RegionDominanceMetadata)
    (irCtx : WfIRContext OpCode)
    (predecessor block : BlockPtr)
    (predecessorMem : predecessor ∈ metadata.reversePostOrder)
    (edge : block ∈ predecessor.getSuccessors! irCtx.raw) :
    (predecessor, block) ∈ DominanceAnalysis.collectEdges metadata irCtx := by
  unfold DominanceAnalysis.collectEdges
  rw [Std.HashSet.mem_ofList, List.contains_iff_mem, List.mem_flatMap]
  refine ⟨predecessor, ?_, ?_⟩
  · simpa only [Array.mem_toList_iff]
  · rw [List.mem_map]
    exact ⟨block, Array.mem_toList_iff.mpr edge, rfl⟩

/-- A semantic predecessor certificate makes the executable edge check succeed. -/
theorem predecessorIndexIsValid_of_correct
    (metadata : RegionDominanceMetadata)
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (blockIndex : Fin metadata.reversePostOrder.size)
    (predecessorIndex : Nat)
    (indexCorrect : ∀ index : Fin metadata.reversePostOrder.size,
      metadata.blockIndex.get? metadata.reversePostOrder[index.val] = some index.val)
    (correct : PredecessorIndexForBlock
      (regionDominanceReversePostOrder metadata) region irCtx
      blockIndex predecessorIndex) :
    DominanceAnalysis.predecessorIndexIsValid metadata region irCtx
      (DominanceAnalysis.collectEdges metadata irCtx)
      blockIndex.val predecessorIndex = true := by
  obtain ⟨predecessor, rfl, predecessorParent, edge⟩ := correct
  unfold DominanceAnalysis.predecessorIndexIsValid
  rw [Array.getElem?_eq_getElem blockIndex.isLt,
    Array.getElem?_eq_getElem predecessor.isLt]
  change ((metadata.reversePostOrder[predecessor.val].get! irCtx.raw).parent =
    some region) at predecessorParent
  change metadata.reversePostOrder[blockIndex.val] ∈
    metadata.reversePostOrder[predecessor.val].getSuccessors! irCtx.raw at edge
  have edgeIn := collectEdges_complete metadata irCtx
    metadata.reversePostOrder[predecessor.val]
    metadata.reversePostOrder[blockIndex.val]
    (Array.mem_iff_getElem.mpr ⟨predecessor.val, predecessor.isLt, rfl⟩)
    edge
  simp only [predecessorParent, indexCorrect predecessor, decide_true, Bool.true_and]
  exact edgeIn

/-- A successful cached-predecessor check yields the represented CFG edge. -/
theorem predecessorIndexIsValid_correct
    (metadata : RegionDominanceMetadata)
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (blockIndex predecessorIndex : Nat)
    (blockIndexInBounds : blockIndex < metadata.reversePostOrder.size)
    (valid : DominanceAnalysis.predecessorIndexIsValid metadata region irCtx
      (DominanceAnalysis.collectEdges metadata irCtx) blockIndex predecessorIndex = true) :
    ∃ predecessor : Fin metadata.reversePostOrder.size,
      predecessor.val = predecessorIndex ∧
      ((metadata.reversePostOrder[predecessor.val]).get! irCtx.raw).parent = some region ∧
      metadata.reversePostOrder[blockIndex] ∈
        metadata.reversePostOrder[predecessor.val].getSuccessors! irCtx.raw := by
  unfold DominanceAnalysis.predecessorIndexIsValid at valid
  rw [Array.getElem?_eq_getElem blockIndexInBounds] at valid
  split at valid <;> simp_all
  rename_i predecessor predecessorInBounds
  obtain ⟨hin, hpredecessor⟩ := Array.getElem?_eq_some_iff.mp predecessorInBounds
  refine ⟨⟨predecessorIndex, hin⟩, rfl, ?_, ?_⟩
  · simpa only [hpredecessor] using valid.1.1
  · apply collectEdges_sound metadata irCtx
    simpa only [hpredecessor] using valid.2

/-- The region metadata checker establishes every per-block part of its contract. -/
theorem metadataIsValid_block
    (metadata : RegionDominanceMetadata)
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (valid : DominanceAnalysis.metadataIsValid metadata region irCtx = true)
    (blockIndex : Nat)
    (blockIndexInBounds : blockIndex < metadata.reversePostOrder.size) :
    ((metadata.reversePostOrder[blockIndex].get! irCtx.raw).parent = some region) ∧
      metadata.blockIndex.get? metadata.reversePostOrder[blockIndex] = some blockIndex ∧
      (∀ predecessorIndex,
        predecessorIndex ∈ metadata.predecessors[blockIndex]! →
          DominanceAnalysis.predecessorIndexIsValid metadata region irCtx
            (DominanceAnalysis.collectEdges metadata irCtx)
            blockIndex predecessorIndex = true) ∧
      (blockIndex = 0 ∨ ∃ predecessorIndex,
        predecessorIndex ∈ metadata.predecessors[blockIndex]! ∧
          predecessorIndex < blockIndex) := by
  unfold DominanceAnalysis.metadataIsValid at valid
  split at valid <;> simp_all
  have predecessorIndexInBounds : blockIndex < metadata.predecessors.size := by
    omega
  have blockValid := valid.2 blockIndex blockIndexInBounds
  obtain ⟨⟨⟨parent, index⟩, predecessors⟩, earlier⟩ := blockValid
  have predecessorsAtIndex :=
    getElem!_pos metadata.predecessors blockIndex predecessorIndexInBounds
  rw [predecessorsAtIndex] at predecessors earlier
  refine ⟨?_, ?_⟩
  · intro predecessorIndex predecessorMem
    obtain ⟨i, hi, hpredecessor⟩ := Array.mem_iff_getElem.mp predecessorMem
    simpa only [hpredecessor] using predecessors i hi
  · rcases earlier with hentry | ⟨i, hi, hearlier⟩
    · exact Or.inl hentry
    · exact Or.inr ⟨metadata.predecessors[blockIndex][i],
        Array.mem_iff_getElem.mpr ⟨i, hi, rfl⟩, hearlier⟩

/-- Successful validation implies a nonempty RPO headed by the region entry. -/
theorem metadataIsValid_entry
    (metadata : RegionDominanceMetadata)
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (valid : DominanceAnalysis.metadataIsValid metadata region irCtx = true) :
    ∃ _sizePositive : 0 < metadata.reversePostOrder.size,
      (region.get! irCtx.raw).firstBlock = some metadata.reversePostOrder[0]! := by
  unfold DominanceAnalysis.metadataIsValid at valid
  split at valid <;> simp_all
  obtain ⟨sizePositive, firstBlockEq⟩ :=
    Array.getElem?_eq_some_iff.mp ‹metadata.reversePostOrder[0]? = some _›
  refine ⟨sizePositive, ?_⟩
  exact firstBlockEq.symm

/-- The executable metadata check implies the exact CHK metadata contract. -/
theorem metadataIsValid_correct
    (metadata : RegionDominanceMetadata)
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    [NeZero metadata.reversePostOrder.size]
    (valid : DominanceAnalysis.metadataIsValid metadata region irCtx = true) :
    RegionDominanceMetadataCorrectForRegion metadata region irCtx := by
  obtain ⟨_, entry⟩ := metadataIsValid_entry metadata region irCtx valid
  constructor
  · rw [getElem!_pos metadata.reversePostOrder 0 (Nat.pos_of_neZero _)] at entry
    exact entry
  · unfold DominanceAnalysis.metadataIsValid at valid
    split at valid <;> simp_all
  · intro blockIndex
    exact (metadataIsValid_block metadata region irCtx valid
      blockIndex.val blockIndex.isLt).1
  · intro index1 index2 blocksEqual
    have index1Lookup :=
      (metadataIsValid_block metadata region irCtx valid index1.val index1.isLt).2.1
    have index2Lookup :=
      (metadataIsValid_block metadata region irCtx valid index2.val index2.isLt).2.1
    change metadata.reversePostOrder[index1.val] =
      metadata.reversePostOrder[index2.val] at blocksEqual
    rw [blocksEqual, index2Lookup] at index1Lookup
    exact Fin.eq_of_val_eq (Option.some.inj index1Lookup).symm
  · intro blockIndex predecessorIndex predecessorMem
    have predecessorValid :=
      (metadataIsValid_block metadata region irCtx valid
        blockIndex.val blockIndex.isLt).2.2.1 predecessorIndex predecessorMem
    obtain ⟨predecessor, predecessorEq, predecessorParent, edge⟩ :=
      predecessorIndexIsValid_correct metadata region irCtx blockIndex.val predecessorIndex
        blockIndex.isLt predecessorValid
    exact ⟨predecessor, predecessorEq, predecessorParent, edge⟩
  · intro blockIndex blockIsNotEntry
    have earlier :=
      (metadataIsValid_block metadata region irCtx valid
        blockIndex.val blockIndex.isLt).2.2.2
    rcases earlier with isEntry | ⟨predecessorIndex, predecessorMem, predecessorEarlier⟩
    · exact False.elim (blockIsNotEntry isEntry)
    · let predecessor : Fin metadata.reversePostOrder.size :=
        ⟨predecessorIndex, Nat.lt_trans predecessorEarlier blockIndex.isLt⟩
      exact ⟨predecessor, predecessorEarlier, predecessorMem⟩

/-- The executable checker accepts every metadata value satisfying its semantic contract. -/
theorem metadataIsValid_of_correct
    (metadata : RegionDominanceMetadata)
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    [NeZero metadata.reversePostOrder.size]
    (indexCorrect : ∀ index : Fin metadata.reversePostOrder.size,
      metadata.blockIndex.get? metadata.reversePostOrder[index.val] = some index.val)
    (correct : RegionDominanceMetadataCorrectForRegion metadata region irCtx) :
    DominanceAnalysis.metadataIsValid metadata region irCtx = true := by
  unfold DominanceAnalysis.metadataIsValid
  rw [correct.entry_is_first]
  rw [Array.getElem?_eq_getElem (Nat.pos_of_neZero metadata.reversePostOrder.size)]
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · have zeroInBounds := Nat.pos_of_neZero metadata.reversePostOrder.size
      change decide (metadata.reversePostOrder[0]'zeroInBounds =
        metadata.reversePostOrder[0]'zeroInBounds) = true
      simp
    · simp [correct.predecessors_size]
  · rw [List.all_eq_true]
    intro blockIndex blockIndexMem
    rw [List.mem_range] at blockIndexMem
    let blockIndexFin : Fin metadata.reversePostOrder.size :=
      ⟨blockIndex, blockIndexMem⟩
    have blockParent := correct.blocks_parent blockIndexFin
    rw [regionDominanceReversePostOrder_get] at blockParent
    simp only [blockIndexFin] at blockParent
    have blockLookup := indexCorrect blockIndexFin
    simp only [blockIndexFin] at blockLookup
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · simp only [getElem!_pos metadata.reversePostOrder blockIndex blockIndexMem,
        blockParent, blockLookup, decide_true, Bool.true_and]
      rw [Array.all_eq_true]
      intro predecessorArrayIndex predecessorArrayIndexInBounds
      let predecessorIndex := metadata.predecessors[blockIndex]![predecessorArrayIndex]
      exact predecessorIndexIsValid_of_correct metadata region irCtx
        blockIndexFin predecessorIndex indexCorrect
        (correct.predecessors_sound blockIndexFin predecessorIndex
          (Array.mem_iff_getElem.mpr
            ⟨predecessorArrayIndex, predecessorArrayIndexInBounds, rfl⟩))
    · by_cases entry : blockIndex = 0
      · simp [entry]
      · simp only [entry, decide_false, Bool.false_or]
        have entryFin : blockIndexFin.val ≠ 0 := by
          simpa only [blockIndexFin] using entry
        obtain ⟨predecessorIndex, predecessorEarlier, predecessorMem⟩ :=
          correct.earlier_predecessor blockIndexFin entryFin
        have predecessorMem' : predecessorIndex.val ∈
            metadata.predecessors[blockIndex]! := by
          simpa only [blockIndexFin] using predecessorMem
        rw [Array.any_eq_true]
        obtain ⟨arrayIndex, arrayIndexInBounds, predecessorEq⟩ :=
          Array.mem_iff_getElem.mp predecessorMem'
        refine ⟨arrayIndex, arrayIndexInBounds, ?_⟩
        simp only [predecessorEq]
        apply decide_eq_true
        omega

/-- Metadata collection passes validation whenever its DFS output is a lawful RPO. -/
theorem collectMetadata_valid_of_rpo
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    [NeZero (DominanceAnalysis.collectPostOrder region irCtx).reverse.size]
    (rpoCorrect : ReversePostOrderForRegion
      (DominanceAnalysis.collectPostOrder region irCtx).reverse region irCtx) :
    DominanceAnalysis.metadataIsValid
      (DominanceAnalysis.collectMetadata region irCtx) region irCtx = true := by
  let rpo := (DominanceAnalysis.collectPostOrder region irCtx).reverse
  let metadata := DominanceAnalysis.collectMetadata region irCtx
  letI : NeZero metadata.reversePostOrder.size := by
    change NeZero rpo.size
    infer_instance
  apply metadataIsValid_of_correct
  · intro index
    exact buildBlockIndex_get?_of_injective rpo rpoCorrect.injective_rpo index
  · change RegionMetadataForRegion (reversePostOrderVector rpo)
      (DominanceAnalysis.collectPredecessors rpo
        (DominanceAnalysis.buildBlockIndex rpo) irCtx) region irCtx
    exact collectPredecessors_correct_of_rpo rpo region irCtx rpoCorrect

/-- Under the same RPO contract, the checked collector returns the concrete metadata. -/
theorem collectMetadata?_eq_some_of_rpo
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    [NeZero (DominanceAnalysis.collectPostOrder region irCtx).reverse.size]
    (rpoCorrect : ReversePostOrderForRegion
      (DominanceAnalysis.collectPostOrder region irCtx).reverse region irCtx) :
    DominanceAnalysis.collectMetadata? region irCtx =
      some (DominanceAnalysis.collectMetadata region irCtx) := by
  simp [DominanceAnalysis.collectMetadata?,
    collectMetadata_valid_of_rpo region irCtx rpoCorrect]

/-- Metadata collection succeeds for every verified nonempty region. -/
theorem collectMetadata_valid
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (root : OperationPtr)
    (ctxVerified : irCtx.Verified root)
    (regionInBounds : region.InBounds irCtx.raw)
    (entry : BlockPtr)
    (entryEq : (region.get! irCtx.raw).firstBlock = some entry) :
    DominanceAnalysis.metadataIsValid
      (DominanceAnalysis.collectMetadata region irCtx) region irCtx = true := by
  obtain ⟨nonempty, rpoCorrect⟩ := collectPostOrder_reverse_forRegion
    region irCtx root ctxVerified regionInBounds entry entryEq
  letI : NeZero (DominanceAnalysis.collectPostOrder region irCtx).reverse.size :=
    ⟨nonempty⟩
  exact collectMetadata_valid_of_rpo region irCtx rpoCorrect

/-- The checked collector returns metadata for every verified nonempty region. -/
theorem collectMetadata?_eq_some
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (root : OperationPtr)
    (ctxVerified : irCtx.Verified root)
    (regionInBounds : region.InBounds irCtx.raw)
    (entry : BlockPtr)
    (entryEq : (region.get! irCtx.raw).firstBlock = some entry) :
    DominanceAnalysis.collectMetadata? region irCtx =
      some (DominanceAnalysis.collectMetadata region irCtx) := by
  simp [DominanceAnalysis.collectMetadata?,
    collectMetadata_valid region irCtx root ctxVerified regionInBounds entry entryEq]

/-- The concrete collector supplies all structural contracts used by completeness. -/
theorem collectMetadata_solverContracts
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (root : OperationPtr)
    (ctxVerified : irCtx.Verified root)
    (regionInBounds : region.InBounds irCtx.raw)
    (entry : BlockPtr)
    (entryEq : (region.get! irCtx.raw).firstBlock = some entry) :
    let metadata := DominanceAnalysis.collectMetadata region irCtx
    ∃ nonempty : metadata.reversePostOrder.size ≠ 0,
      @RegionDominanceMetadataCorrectForRegion OpCode inferInstance
          metadata region irCtx ⟨nonempty⟩ ∧
        PredecessorTableCompleteForRegion
          (regionDominanceReversePostOrder metadata) metadata.predecessors irCtx ∧
        ReachableBlocksRepresented
          (regionDominanceReversePostOrder metadata) region irCtx := by
  let reversePostOrder := (DominanceAnalysis.collectPostOrder region irCtx).reverse
  let metadata := DominanceAnalysis.collectMetadata region irCtx
  obtain ⟨nonempty, rpoCorrect⟩ := collectPostOrder_reverse_forRegion
    region irCtx root ctxVerified regionInBounds entry entryEq
  letI : NeZero reversePostOrder.size := ⟨nonempty⟩
  refine ⟨nonempty, ?_, ?_, ?_⟩
  · change RegionMetadataForRegion (reversePostOrderVector reversePostOrder)
      (DominanceAnalysis.collectPredecessors reversePostOrder
        (DominanceAnalysis.buildBlockIndex reversePostOrder) irCtx) region irCtx
    exact collectPredecessors_correct_of_rpo reversePostOrder region irCtx rpoCorrect
  · change PredecessorTableCompleteForRegion (reversePostOrderVector reversePostOrder)
      (DominanceAnalysis.collectPredecessors reversePostOrder
        (DominanceAnalysis.buildBlockIndex reversePostOrder) irCtx) irCtx
    exact collectPredecessors_complete_of_rpo reversePostOrder irCtx
      rpoCorrect.injective_rpo
  · change ReachableBlocksRepresented
      (reversePostOrderVector reversePostOrder) region irCtx
    exact collectPostOrder_reverse_reachable region irCtx root ctxVerified
      regionInBounds entry entryEq

/-- Any metadata returned by the checked collector satisfies the semantic contract. -/
theorem collectMetadata?_correct
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (metadata : RegionDominanceMetadata)
    [NeZero metadata.reversePostOrder.size]
    (collected : DominanceAnalysis.collectMetadata? region irCtx = some metadata) :
    RegionDominanceMetadataCorrectForRegion metadata region irCtx := by
  cases valid : DominanceAnalysis.metadataIsValid
      (DominanceAnalysis.collectMetadata region irCtx) region irCtx with
  | false => simp [DominanceAnalysis.collectMetadata?, valid] at collected
  | true =>
    simp only [DominanceAnalysis.collectMetadata?, valid, ite_true] at collected
    have metadataEq := Option.some.inj collected
    subst metadata
    exact metadataIsValid_correct
      (DominanceAnalysis.collectMetadata region irCtx) region irCtx valid

/-- The checked collector supplies both nonemptiness and its semantic contract. -/
theorem collectMetadata?_certified
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (metadata : RegionDominanceMetadata)
    (collected : DominanceAnalysis.collectMetadata? region irCtx = some metadata) :
    RegionDominanceMetadataCertifiedForRegion metadata region irCtx := by
  cases valid : DominanceAnalysis.metadataIsValid
      (DominanceAnalysis.collectMetadata region irCtx) region irCtx with
  | false => simp [DominanceAnalysis.collectMetadata?, valid] at collected
  | true =>
    simp only [DominanceAnalysis.collectMetadata?, valid, ite_true] at collected
    have metadataEq := Option.some.inj collected
    subst metadata
    obtain ⟨sizePositive, _⟩ := metadataIsValid_entry
      (DominanceAnalysis.collectMetadata region irCtx) region irCtx valid
    letI : NeZero (DominanceAnalysis.collectMetadata region irCtx).reversePostOrder.size :=
      ⟨Nat.ne_of_gt sizePositive⟩
    exact ⟨Nat.ne_of_gt sizePositive,
      metadataIsValid_correct
        (DominanceAnalysis.collectMetadata region irCtx) region irCtx valid⟩

/-- Two solver values encode the same working parents below an RPO boundary. -/
def AgreesBefore
    (value1 value2 : DominanceValue blockCount)
    (nextIndex : Nat) : Prop :=
  ∀ blockIndex : Fin blockCount,
    blockIndex.val < nextIndex → value1.get! blockIndex.val = value2.get! blockIndex.val

/-- Every block at or after an RPO boundary is still unknown. -/
def UninitializedFrom
    (value : DominanceValue blockCount)
    (nextIndex : Nat) : Prop :=
  ∀ blockIndex : Fin blockCount,
    nextIndex ≤ blockIndex.val → value.get! blockIndex.val = blockCount

/-- Invariants after processing every RPO index below `nextIndex`. -/
structure SweepInvariantForRegion [HasOpInfo OpInfo]
    (value : DominanceValue blockCount)
    (reversePostOrder : Vector BlockPtr blockCount)
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo)
    (nextIndex : Nat) : Prop where
  forest : WorkingForestForRegion value reversePostOrder region irCtx
  sound : SoundForRegion value reversePostOrder region irCtx
  initialized_before : ∀ blockIndex : Fin blockCount,
    blockIndex.val < nextIndex → Initialized value blockIndex

/--
The stronger invariant used only during the first sweep. Unprocessed blocks
remain unknown, while every processed CHK equation is stable under arbitrary
later-RPO refinements.
-/
structure InitialSweepInvariantForRegion [HasOpInfo OpInfo]
    (value : DominanceValue blockCount)
    (reversePostOrder : Vector BlockPtr blockCount)
    (predecessors : Array (Array Nat))
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo)
    (nextIndex : Nat) : Prop where
  sweep : SweepInvariantForRegion value reversePostOrder region irCtx nextIndex
  uninitialized_from : UninitializedFrom value nextIndex
  prefix_fixed : ∀ (future : DominanceValue blockCount),
    future ≠ ⊥ →
    AgreesBefore value future nextIndex →
    ∀ blockIndex : Fin blockCount,
      blockIndex.val < nextIndex →
      blockIndex.val ≠ 0 →
      (DominanceAnalysis.computeImmediateDominator
        blockIndex.val predecessors future).1 = future.get? blockIndex.val

/-- A path represented entirely by RPO indices no later than its target. -/
def IndexedEntryPath [HasOpInfo OpInfo] [NeZero blockCount]
    (reversePostOrder : Vector BlockPtr blockCount)
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo)
    (targetIndex : Fin blockCount) : Prop :=
  ∃ blocks,
    region.Path irCtx
      (reversePostOrder.get ⟨0, Nat.pos_of_neZero blockCount⟩)
      (reversePostOrder.get targetIndex) blocks ∧
    ∀ block ∈ blocks,
      ∃ blockIndex : Fin blockCount,
        blockIndex ≤ targetIndex ∧ reversePostOrder.get blockIndex = block

/-- The optional accumulator of the executable predecessor fold is semantically sound. -/
def CandidateStateForBlock [HasOpInfo OpInfo]
    (value : DominanceValue blockCount)
    (reversePostOrder : Vector BlockPtr blockCount)
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo)
    (blockIndex : Fin blockCount)
    (candidate : Option Nat) : Prop :=
  candidate = none ∨
    ∃ immediateDominator : Fin blockCount,
      candidate = some immediateDominator.val ∧
      PartialCandidateForBlock value reversePostOrder region irCtx
        blockIndex immediateDominator

/-- An optional executable candidate is initialized and no later than `upperBound`. -/
def CandidateBoundedBy
    (value : DominanceValue blockCount)
    (upperBound : Fin blockCount)
    (candidate : Option Nat) : Prop :=
  ∃ immediateDominator : Fin blockCount,
    candidate = some immediateDominator.val ∧
    Initialized value immediateDominator ∧
    immediateDominator ≤ upperBound

/-- The optional fold candidate is a working ancestor of one processed predecessor. -/
def CandidateAncestorOf
    (value : DominanceValue blockCount)
    (predecessorIndex : Nat)
    (candidate : Option Nat) : Prop :=
  ∃ candidateIndex,
    candidate = some candidateIndex ∧
      WorkingAncestor value candidateIndex predecessorIndex

/-- An optional predecessor-fold candidate lies below the current RPO boundary. -/
def CandidateBefore (candidate : Option Nat) (nextIndex : Nat) : Prop :=
  candidate = none ∨ ∃ candidateIndex, candidate = some candidateIndex ∧ candidateIndex < nextIndex

/-- The unknown region value contains every semantic immediate dominator. -/
theorem top_soundForRegion [HasOpInfo OpInfo]
    (reversePostOrder : Vector BlockPtr blockCount)
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo) :
    SoundForRegion (⊤ : DominanceValue blockCount) reversePostOrder region irCtx := by
  intro blockIndex dominatorIndex _
  rw [gamma_top]
  trivial

/-- The earlier-predecessor metadata constructs an entry path to every represented block. -/
theorem RegionMetadataForRegion.indexedEntryPath [HasOpInfo OpInfo] [NeZero blockCount]
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (targetIndex : Fin blockCount) :
    IndexedEntryPath reversePostOrder region irCtx targetIndex := by
  by_cases hentry : targetIndex.val = 0
  · have htarget : targetIndex = ⟨0, Nat.pos_of_neZero blockCount⟩ :=
      Fin.eq_of_val_eq hentry
    subst targetIndex
    refine ⟨[reversePostOrder.get ⟨0, Nat.pos_of_neZero blockCount⟩], ?_, ?_⟩
    · exact .Single (metadata.blocks_parent _)
    · intro block hmem
      simp only [List.mem_singleton] at hmem
      subst block
      exact ⟨⟨0, Nat.pos_of_neZero blockCount⟩, Nat.le_refl _, rfl⟩
  · obtain ⟨predecessorIndex, hpredecessor, hmem⟩ :=
      metadata.earlier_predecessor targetIndex hentry
    obtain ⟨blocks, path, indexed⟩ := metadata.indexedEntryPath predecessorIndex
    obtain ⟨representedPredecessor, hrepresented, predecessorParent, edge⟩ :=
      metadata.predecessors_sound targetIndex predecessorIndex.val hmem
    have hrepresentedPredecessor : representedPredecessor = predecessorIndex :=
      Fin.eq_of_val_eq hrepresented
    subst representedPredecessor
    have edgePath : region.Path irCtx
        (reversePostOrder.get predecessorIndex)
        (reversePostOrder.get targetIndex)
        [reversePostOrder.get predecessorIndex, reversePostOrder.get targetIndex] :=
      .Cons predecessorParent edge (.Single (metadata.blocks_parent targetIndex))
    refine ⟨blocks ++ [reversePostOrder.get targetIndex], path.append edgePath, ?_⟩
    intro block blockMem
    simp only [List.mem_append, List.mem_singleton] at blockMem
    rcases blockMem with oldBlock | targetBlock
    · obtain ⟨blockIndex, hle, hblock⟩ := indexed block oldBlock
      exact ⟨blockIndex, Nat.le_trans hle (Nat.le_of_lt hpredecessor), hblock⟩
    · subst block
      exact ⟨targetIndex, Nat.le_refl _, rfl⟩
termination_by targetIndex.val
decreasing_by exact hpredecessor

/-- The metadata's rooted order places every semantic dominator no later than its block. -/
theorem RegionMetadataForRegion.orderedForRegion [HasOpInfo OpInfo] [NeZero blockCount]
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx) :
    OrderedForRegion reversePostOrder region irCtx := by
  intro dominatorIndex dominatedIndex dominance
  rcases dominance with heq | properDominance
  · exact Fin.le_of_eq (metadata.injective_rpo heq)
  · obtain ⟨blocks, path, indexed⟩ := metadata.indexedEntryPath dominatedIndex
    have dominatorMem := properDominance.mem_of_entry_path metadata.entry_is_first path
    obtain ⟨representedDominator, hle, hrepresented⟩ :=
      indexed (reversePostOrder.get dominatorIndex) dominatorMem
    have hindices : representedDominator = dominatorIndex :=
      metadata.injective_rpo hrepresented
    subst representedDominator
    exact hle

/-- The CHK entry-only initial value is a valid working forest. -/
theorem initial_workingForestForRegion [HasOpInfo OpInfo] [NeZero blockCount]
    (reversePostOrder : Vector BlockPtr blockCount)
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo) :
    WorkingForestForRegion
      (initial blockCount) reversePostOrder region irCtx := by
  have hpositive : 0 < blockCount := Nat.pos_of_neZero blockCount
  let entryIndex : Fin blockCount := ⟨0, hpositive⟩
  have entryInitialized : Initialized (initial blockCount) entryIndex := by
    refine ⟨entryIndex, ?_⟩
    rw [get?_initial]
    rfl
  constructor
  · apply refine_ne_bottom (⊤ : DominanceValue blockCount)
    · intro hbottom
      change DominanceValue.state _ = DominanceValue.bottom at hbottom
      contradiction
  · intro blockIndex immediateDominator hget
    rw [get?_initial] at hget
    by_cases hentry : blockIndex.val = 0
    · left
      constructor
      · exact hentry
      · simp only [hentry] at hget
        exact Option.some.inj hget |>.symm
    · simp only [hentry] at hget
      contradiction

  · intro blockIndex immediateDominator hget
    rw [get?_initial] at hget
    by_cases hentry : blockIndex.val = 0
    · simp only [hentry] at hget
      have himmediate : immediateDominator = entryIndex := by
        apply Fin.eq_of_val_eq
        exact Option.some.inj hget |>.symm
      subst immediateDominator
      exact entryInitialized
    · simp only [hentry] at hget
      contradiction
  · intro blockIndex immediateDominator dominatorIndex hget _ dominates
    rw [get?_initial] at hget
    by_cases hentry : blockIndex.val = 0
    · simp only [hentry] at hget
      have hblock : blockIndex = entryIndex := Fin.eq_of_val_eq hentry
      have himmediate : immediateDominator = entryIndex := by
        apply Fin.eq_of_val_eq
        exact Option.some.inj hget |>.symm
      subst blockIndex
      subst immediateDominator
      exact dominates
    · simp only [hentry] at hget
      contradiction

/-- Before the first sweep, every non-entry RPO block is unknown. -/
theorem initial_uninitializedFrom [NeZero blockCount] :
    UninitializedFrom (initial blockCount) 1 := by
  intro blockIndex blockNotEntry
  have hne : blockIndex.val ≠ 0 := by omega
  have hnotBottom : initial blockCount ≠ ⊥ := by
    unfold initial
    apply refine_ne_bottom
    intro hbottom
    change DominanceValue.state _ = DominanceValue.bottom at hbottom
    contradiction
  have hle := get!_le_blockCount (initial blockCount) blockIndex
  by_cases sentinel : (initial blockCount).get! blockIndex.val = blockCount
  · exact sentinel
  · have hlt : (initial blockCount).get! blockIndex.val < blockCount := by omega
    have initialized := get?_eq_some_get! (initial blockCount) hnotBottom blockIndex hlt
    rw [get?_initial] at initialized
    simp only [hne, ↓reduceIte] at initialized
    contradiction

/-- Refining one entry of a consistent state preserves every initialized index. -/
theorem Initialized.refine
    {value : DominanceValue blockCount}
    (initialized : Initialized value queriedIndex)
    (hvalue : value ≠ ⊥)
    (blockIndex immediateDominator : Fin blockCount) :
    Initialized (value.refine! blockIndex.val immediateDominator.val) queriedIndex := by
  obtain ⟨oldImmediateDominator, hget⟩ := initialized
  by_cases hsame : queriedIndex = blockIndex
  · subst queriedIndex
    let refinedImmediateDominator : Fin blockCount :=
      ⟨min oldImmediateDominator.val immediateDominator.val,
        Nat.lt_of_le_of_lt (Nat.min_le_left _ _) oldImmediateDominator.isLt⟩
    refine ⟨refinedImmediateDominator, ?_⟩
    rw [get?_refine_eq_some_min value hvalue blockIndex immediateDominator]
    have hold := get!_eq_of_get?_eq_some value blockIndex oldImmediateDominator hget
    simp only [refinedImmediateDominator]
    rw [hold]
  · refine ⟨oldImmediateDominator, ?_⟩
    rw [get?_refine_of_ne value hvalue blockIndex queriedIndex immediateDominator hsame]
    exact hget

/-- Refining an in-bounds block with an in-bounds candidate initializes that block. -/
theorem initialized_refine_target
    {value : DominanceValue blockCount}
    (hvalue : value ≠ ⊥)
    (blockIndex immediateDominator : Fin blockCount) :
    Initialized (value.refine! blockIndex.val immediateDominator.val) blockIndex := by
  let refinedImmediateDominator : Fin blockCount :=
    ⟨min (value.get! blockIndex.val) immediateDominator.val,
      Nat.lt_of_le_of_lt (Nat.min_le_right _ _) immediateDominator.isLt⟩
  refine ⟨refinedImmediateDominator, ?_⟩
  rw [get?_refine_eq_some_min value hvalue blockIndex immediateDominator]

/--
Refining one block with a valid working-parent candidate preserves the CHK
working-forest invariant.
-/
theorem WorkingForestForRegion.refine [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (blockIndex immediateDominator : Fin blockCount)
    (candidateInitialized : Initialized value immediateDominator)
    (candidateDecreases :
      (blockIndex.val = 0 ∧ immediateDominator.val = 0) ∨
        immediateDominator < blockIndex)
    (candidatePreserves : ∀ dominatorIndex : Fin blockCount,
      dominatorIndex < blockIndex →
      (reversePostOrder.get dominatorIndex).DominatesInSSACFGRegion
        (reversePostOrder.get blockIndex) region irCtx →
      (reversePostOrder.get dominatorIndex).DominatesInSSACFGRegion
        (reversePostOrder.get immediateDominator) region irCtx) :
    WorkingForestForRegion
      (value.refine! blockIndex.val immediateDominator.val)
      reversePostOrder region irCtx := by
  let refinedValue := value.refine! blockIndex.val immediateDominator.val
  have initializedAfterRefinement : ∀ queriedIndex : Fin blockCount,
      Initialized value queriedIndex → Initialized refinedValue queriedIndex := by
    intro queriedIndex initialized
    exact initialized.refine forest.not_bottom blockIndex immediateDominator
  have targetParent : ∀ queriedParent : Fin blockCount,
      refinedValue.get? blockIndex.val = some queriedParent.val →
      queriedParent = immediateDominator ∨
        ∃ oldParent : Fin blockCount,
          value.get? blockIndex.val = some oldParent.val ∧ queriedParent = oldParent := by
    intro queriedParent hget
    dsimp only [refinedValue] at hget
    rw [get?_refine_eq_some_min value forest.not_bottom blockIndex immediateDominator] at hget
    have hparent := Option.some.inj hget
    by_cases hincoming : immediateDominator.val ≤ value.get! blockIndex.val
    · left
      apply Fin.eq_of_val_eq
      rw [Nat.min_eq_right hincoming] at hparent
      exact hparent.symm
    · have holdLt : value.get! blockIndex.val < blockCount :=
        Nat.lt_of_lt_of_le (Nat.lt_of_not_ge hincoming)
          (Nat.le_of_lt immediateDominator.isLt)
      let oldParent : Fin blockCount := ⟨value.get! blockIndex.val, holdLt⟩
      right
      refine ⟨oldParent, ?_, ?_⟩
      · exact get?_eq_some_get! value forest.not_bottom blockIndex holdLt
      · apply Fin.eq_of_val_eq
        rw [Nat.min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hincoming))] at hparent
        exact hparent.symm
  constructor
  · exact refine_ne_bottom value forest.not_bottom blockIndex.val immediateDominator.val
  · intro queriedBlock queriedParent hget
    by_cases hsame : queriedBlock = blockIndex
    · subst queriedBlock
      rcases targetParent queriedParent hget with hcandidate | ⟨oldParent, hold, hparent⟩
      · subst queriedParent
        exact candidateDecreases
      · subst queriedParent
        exact forest.parent_decreases blockIndex oldParent hold
    · have hold : value.get? queriedBlock.val = some queriedParent.val := by
        rw [← get?_refine_of_ne value forest.not_bottom blockIndex queriedBlock
          immediateDominator hsame]
        exact hget
      exact forest.parent_decreases queriedBlock queriedParent hold
  · intro queriedBlock queriedParent hget
    by_cases hsame : queriedBlock = blockIndex
    · subst queriedBlock
      rcases targetParent queriedParent hget with hcandidate | ⟨oldParent, hold, hparent⟩
      · subst queriedParent
        exact initializedAfterRefinement immediateDominator candidateInitialized
      · subst queriedParent
        exact initializedAfterRefinement oldParent
          (forest.parent_initialized blockIndex oldParent hold)
    · have hold : value.get? queriedBlock.val = some queriedParent.val := by
        rw [← get?_refine_of_ne value forest.not_bottom blockIndex queriedBlock
          immediateDominator hsame]
        exact hget
      exact initializedAfterRefinement queriedParent
        (forest.parent_initialized queriedBlock queriedParent hold)
  · intro queriedBlock queriedParent dominatorIndex hget hstrict dominates
    by_cases hsame : queriedBlock = blockIndex
    · subst queriedBlock
      rcases targetParent queriedParent hget with hcandidate | ⟨oldParent, hold, hparent⟩
      · subst queriedParent
        exact candidatePreserves dominatorIndex hstrict dominates
      · subst queriedParent
        exact forest.preserves_strict_dominators blockIndex oldParent dominatorIndex
          hold hstrict dominates
    · have hold : value.get? queriedBlock.val = some queriedParent.val := by
        rw [← get?_refine_of_ne value forest.not_bottom blockIndex queriedBlock
          immediateDominator hsame]
        exact hget
      exact forest.preserves_strict_dominators queriedBlock queriedParent dominatorIndex
        hold hstrict dominates

/--
A pointwise refinement remains semantically sound when its incoming bound still
contains the block's semantic immediate dominator.
-/
theorem SoundForRegion.refine [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (sound : SoundForRegion value reversePostOrder region irCtx)
    (blockIndex immediateDominator : Fin blockCount)
    (incomingSound : ∀ dominatorIndex,
      (reversePostOrder.get dominatorIndex).ImmediateDominatorInSSACFGRegion
        (reversePostOrder.get blockIndex) region irCtx →
      dominatorIndex ≤ immediateDominator) :
    SoundForRegion
      (value.refine! blockIndex.val immediateDominator.val)
      reversePostOrder region irCtx := by
  intro queriedBlock queriedDominator semanticIDom
  have oldSound := sound queriedBlock queriedDominator semanticIDom
  cases value with
  | bottom => exact False.elim oldSound
  | state immediateDominators =>
      change queriedDominator.val ≤ immediateDominators[queriedBlock.val].val at oldSound
      simp only [refine!, immediateDominator.isLt, dite_eq_left, γ]
      change queriedDominator.val ≤
        (immediateDominators.set! blockIndex.val _)[queriedBlock.val].val
      rw [Vector.getElem_set! queriedBlock.isLt]
      split
      · rename_i hsame
        have : queriedBlock = blockIndex := Fin.eq_of_val_eq hsame.symm
        subst queriedBlock
        change queriedDominator.val ≤
          min immediateDominators[blockIndex.val]!.val immediateDominator.val
        have incomingBound := incomingSound queriedDominator semanticIDom
        have oldBound := congrArg Fin.val
          (getElem!_pos immediateDominators blockIndex.val blockIndex.isLt)
        omega
      · exact oldSound

/-- One executable CHK refinement preserves both region-level invariants. -/
theorem refine_preserves_invariants [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (sound : SoundForRegion value reversePostOrder region irCtx)
    (blockIndex immediateDominator : Fin blockCount)
    (candidate : UpdateCandidateForBlock value reversePostOrder region irCtx
      blockIndex immediateDominator) :
    WorkingForestForRegion
        (value.refine! blockIndex.val immediateDominator.val)
        reversePostOrder region irCtx ∧
      SoundForRegion
        (value.refine! blockIndex.val immediateDominator.val)
        reversePostOrder region irCtx := by
  constructor
  · exact forest.refine blockIndex immediateDominator candidate.initialized
      candidate.decreases candidate.preserves_strict_dominators
  · exact sound.refine blockIndex immediateDominator candidate.contains_immediate_dominator

/--
The CHK entry-only initial value contains every semantic immediate dominator
when RPO index zero is the region entry.
-/
theorem initial_soundForRegion [HasOpInfo OpInfo] [NeZero blockCount]
    (reversePostOrder : Vector BlockPtr blockCount)
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo)
    (entryIsFirst : (region.get! irCtx.raw).firstBlock =
      some (reversePostOrder.get ⟨0, Nat.pos_of_neZero blockCount⟩)) :
    SoundForRegion (initial blockCount) reversePostOrder region irCtx := by
  let entryIndex : Fin blockCount := ⟨0, Nat.pos_of_neZero blockCount⟩
  have topSound := top_soundForRegion reversePostOrder region irCtx
  have initialSound := topSound.refine entryIndex entryIndex (by
    intro dominatorIndex semanticIDom
    unfold BlockPtr.ImmediateDominatorInSSACFGRegion at semanticIDom
    exact False.elim (semanticIDom.1.false_of_dominated_is_entry entryIsFirst))
  exact initialSound

/-- Correct fixed metadata establishes both invariants for the CHK initial state. -/
theorem RegionMetadataForRegion.initial_invariants [HasOpInfo OpInfo] [NeZero blockCount]
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx) :
    WorkingForestForRegion
        (initial blockCount) reversePostOrder region irCtx ∧
      SoundForRegion
        (initial blockCount) reversePostOrder region irCtx := by
  exact ⟨initial_workingForestForRegion reversePostOrder region irCtx,
    initial_soundForRegion reversePostOrder region irCtx metadata.entry_is_first⟩

/-- Initialization establishes the sweep invariant immediately after the entry index. -/
theorem RegionMetadataForRegion.initial_sweepInvariant [HasOpInfo OpInfo]
    [NeZero blockCount]
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx) :
    SweepInvariantForRegion
      (initial blockCount) reversePostOrder region irCtx 1 := by
  obtain ⟨forest, sound⟩ := metadata.initial_invariants
  refine ⟨forest, sound, ?_⟩
  intro blockIndex hbefore
  have hzero : blockIndex.val = 0 := by omega
  let entryIndex : Fin blockCount := ⟨0, Nat.pos_of_neZero blockCount⟩
  have hblock : blockIndex = entryIndex := Fin.eq_of_val_eq hzero
  subst blockIndex
  refine ⟨entryIndex, ?_⟩
  rw [get?_initial]
  rfl

/-- Initialization establishes the stronger invariant needed for the first sweep. -/
theorem RegionMetadataForRegion.initial_firstSweepInvariant [HasOpInfo OpInfo]
    [NeZero blockCount]
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx) :
    InitialSweepInvariantForRegion
      (initial blockCount) reversePostOrder predecessors region irCtx 1 := by
  refine ⟨metadata.initial_sweepInvariant, initial_uninitializedFrom, ?_⟩
  intro future _ _ blockIndex blockBefore blockNotEntry
  omega

/-- A semantic immediate dominator has a strictly earlier RPO index. -/
theorem immediateDominator_index_lt [HasOpInfo OpInfo]
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (ordered : OrderedForRegion reversePostOrder region irCtx)
    (blockIndex dominatorIndex : Fin blockCount)
    (semanticIDom :
      (reversePostOrder.get dominatorIndex).ImmediateDominatorInSSACFGRegion
        (reversePostOrder.get blockIndex) region irCtx) :
    dominatorIndex < blockIndex := by
  have hle := ordered dominatorIndex blockIndex (Or.inr semanticIDom.1)
  have hne : dominatorIndex ≠ blockIndex := by
    intro heq
    have hpointers := congrArg reversePostOrder.get heq
    exact semanticIDom.1.ne hpointers
  have hneVal : dominatorIndex.val ≠ blockIndex.val := by
    intro heq
    exact hne (Fin.eq_of_val_eq heq)
  omega

/-- An initialized CFG predecessor is a sound partial CHK candidate. -/
theorem PartialCandidateForBlock.of_predecessor [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (injectiveRPO : InjectiveRPO reversePostOrder)
    (ordered : OrderedForRegion reversePostOrder region irCtx)
    (blockIndex predecessorIndex : Fin blockCount)
    (predecessorParent :
      ((reversePostOrder.get predecessorIndex).get! irCtx.raw).parent = some region)
    (edge : reversePostOrder.get blockIndex ∈
      (reversePostOrder.get predecessorIndex).getSuccessors! irCtx.raw)
    (initialized : Initialized value predecessorIndex) :
    PartialCandidateForBlock value reversePostOrder region irCtx
      blockIndex predecessorIndex := by
  constructor
  · exact initialized
  · intro dominatorIndex hstrict dominates
    have properDominance :
        (reversePostOrder.get dominatorIndex).ProperlyDominatesInSSACFGRegion
          (reversePostOrder.get blockIndex) region irCtx := by
      rcases dominates with heq | proper
      · have hindices : dominatorIndex = blockIndex := injectiveRPO heq
        exact False.elim (Fin.ne_of_lt hstrict hindices)
      · exact proper
    exact properDominance.dominates_predecessor predecessorParent edge
  · intro dominatorIndex semanticIDom
    have dominatesPredecessor :=
      semanticIDom.1.dominates_predecessor predecessorParent edge
    exact ordered dominatorIndex predecessorIndex dominatesPredecessor

/--
`intersect` preserves any semantic dominator shared by its two initialized
input blocks.
-/
theorem WorkingForestForRegion.intersect_preserves_dominator [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (ordered : OrderedForRegion reversePostOrder region irCtx)
    (dominatorIndex index1 index2 : Fin blockCount)
    (initialized1 : Initialized value index1)
    (initialized2 : Initialized value index2)
    (dominates1 : (reversePostOrder.get dominatorIndex).DominatesInSSACFGRegion
      (reversePostOrder.get index1) region irCtx)
    (dominates2 : (reversePostOrder.get dominatorIndex).DominatesInSSACFGRegion
      (reversePostOrder.get index2) region irCtx) :
    ∃ result : Fin blockCount,
      value.intersect index1.val index2.val = result.val ∧
      Initialized value result ∧
      (reversePostOrder.get dominatorIndex).DominatesInSSACFGRegion
        (reversePostOrder.get result) region irCtx := by
  let property : Nat → Prop := fun index =>
    ∃ blockIndex : Fin blockCount,
      blockIndex.val = index ∧
      Initialized value blockIndex ∧
      (reversePostOrder.get dominatorIndex).DominatesInSSACFGRegion
        (reversePostOrder.get blockIndex) region irCtx
  have lowerBound : ∀ index, property index → dominatorIndex.val ≤ index := by
    intro index ⟨blockIndex, hindex, _, dominates⟩
    rw [← hindex]
    exact ordered dominatorIndex blockIndex dominates
  have step : ∀ index, dominatorIndex.val < index →
      property index → property (value.get! index) := by
    intro index habove ⟨blockIndex, hindex, initialized, dominates⟩
    subst index
    obtain ⟨immediateDominator, hget⟩ := initialized
    refine ⟨immediateDominator, ?_, forest.parent_initialized blockIndex _ hget, ?_⟩
    · exact (get!_eq_of_get?_eq_some value blockIndex immediateDominator hget).symm
    · exact forest.preserves_strict_dominators blockIndex immediateDominator dominatorIndex
        hget habove dominates
  have preserved := value.intersect_preserves_above dominatorIndex.val property lowerBound step
    ⟨index1, rfl, initialized1, dominates1⟩
    ⟨index2, rfl, initialized2, dominates2⟩
  obtain ⟨result, hresult, initialized, dominates⟩ := preserved
  exact ⟨result, hresult.symm, initialized, dominates⟩

/-- Intersecting initialized indices returns another initialized forest index. -/
theorem WorkingForestForRegion.intersect_initialized [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (index1 index2 : Fin blockCount)
    (initialized1 : Initialized value index1)
    (initialized2 : Initialized value index2) :
    ∃ result : Fin blockCount,
      value.intersect index1.val index2.val = result.val ∧
        Initialized value result := by
  let property : Nat → Prop := fun index =>
    ∃ blockIndex : Fin blockCount,
      blockIndex.val = index ∧ Initialized value blockIndex
  have step : ∀ index, property index → property (value.get! index) := by
    intro index ⟨blockIndex, hindex, initialized⟩
    subst index
    obtain ⟨immediateDominator, hget⟩ := initialized
    refine ⟨immediateDominator, ?_, forest.parent_initialized blockIndex _ hget⟩
    exact (get!_eq_of_get?_eq_some value blockIndex immediateDominator hget).symm
  have preserved := value.intersect_preserves property step
    ⟨index1, rfl, initialized1⟩ ⟨index2, rfl, initialized2⟩
  obtain ⟨result, hresult, initialized⟩ := preserved
  exact ⟨result, hresult.symm, initialized⟩

/-- The common ancestor returned by `intersect` is no later than either input. -/
theorem WorkingForestForRegion.intersect_le_inputs [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (index1 index2 : Fin blockCount)
    (initialized1 : Initialized value index1)
    (initialized2 : Initialized value index2) :
    value.intersect index1.val index2.val ≤ index1.val ∧
      value.intersect index1.val index2.val ≤ index2.val := by
  let valid : Nat → Prop := fun index =>
    ∃ blockIndex : Fin blockCount,
      blockIndex.val = index ∧ Initialized value blockIndex
  have parentValid : ∀ index, valid index → valid (value.get! index) := by
    intro index ⟨blockIndex, hindex, initialized⟩
    subst index
    obtain ⟨immediateDominator, hget⟩ := initialized
    refine ⟨immediateDominator, ?_, forest.parent_initialized blockIndex _ hget⟩
    exact (get!_eq_of_get?_eq_some value blockIndex immediateDominator hget).symm
  have parentDecreases : ∀ index, valid index → 0 < index → value.get! index < index := by
    intro index ⟨blockIndex, hindex, initialized⟩ hpositive
    subst index
    obtain ⟨immediateDominator, hget⟩ := initialized
    rw [get!_eq_of_get?_eq_some value blockIndex immediateDominator hget]
    rcases forest.parent_decreases blockIndex immediateDominator hget with hentry | hdecreases
    · omega
    · exact hdecreases
  exact value.intersect_le_inputs valid parentValid parentDecreases
    ⟨index1, rfl, initialized1⟩ ⟨index2, rfl, initialized2⟩

/-- The common ancestor returned by `intersect` is on both working-parent chains. -/
theorem WorkingForestForRegion.intersect_ancestor_inputs [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (index1 index2 : Fin blockCount)
    (initialized1 : Initialized value index1)
    (initialized2 : Initialized value index2) :
    WorkingAncestor value (value.intersect index1.val index2.val) index1.val ∧
      WorkingAncestor value (value.intersect index1.val index2.val) index2.val := by
  let valid : Nat → Prop := fun index =>
    ∃ blockIndex : Fin blockCount,
      blockIndex.val = index ∧ Initialized value blockIndex
  have parentValid : ∀ index, valid index → valid (value.get! index) := by
    intro index ⟨blockIndex, hindex, initialized⟩
    subst index
    obtain ⟨immediateDominator, hget⟩ := initialized
    refine ⟨immediateDominator, ?_, forest.parent_initialized blockIndex _ hget⟩
    exact (get!_eq_of_get?_eq_some value blockIndex immediateDominator hget).symm
  have parentDecreases : ∀ index, valid index → 0 < index → value.get! index < index := by
    intro index ⟨blockIndex, hindex, initialized⟩ hpositive
    subst index
    obtain ⟨immediateDominator, hget⟩ := initialized
    rw [get!_eq_of_get?_eq_some value blockIndex immediateDominator hget]
    rcases forest.parent_decreases blockIndex immediateDominator hget with hentry | hdecreases
    · omega
    · exact hdecreases
  exact value.intersect_ancestor_inputs valid parentValid parentDecreases
    ⟨index1, rfl, initialized1⟩ ⟨index2, rfl, initialized2⟩

/-- Intersecting two partial predecessor candidates produces another partial candidate. -/
theorem PartialCandidateForBlock.intersect [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (ordered : OrderedForRegion reversePostOrder region irCtx)
    (blockIndex candidate1 candidate2 : Fin blockCount)
    (first : PartialCandidateForBlock value reversePostOrder region irCtx
      blockIndex candidate1)
    (second : PartialCandidateForBlock value reversePostOrder region irCtx
      blockIndex candidate2) :
    ∃ result : Fin blockCount,
      value.intersect candidate1.val candidate2.val = result.val ∧
        PartialCandidateForBlock value reversePostOrder region irCtx blockIndex result := by
  obtain ⟨result, hresult, resultInitialized⟩ :=
    forest.intersect_initialized candidate1 candidate2 first.initialized second.initialized
  refine ⟨result, hresult, ?_⟩
  constructor
  · exact resultInitialized
  · intro dominatorIndex hstrict dominates
    obtain ⟨semanticResult, hsemanticResult, _, resultDominance⟩ :=
      forest.intersect_preserves_dominator ordered dominatorIndex candidate1 candidate2
        first.initialized second.initialized
        (first.preserves_strict_dominators dominatorIndex hstrict dominates)
        (second.preserves_strict_dominators dominatorIndex hstrict dominates)
    have heq : semanticResult = result := by
      apply Fin.eq_of_val_eq
      exact hsemanticResult.symm.trans hresult
    subst semanticResult
    exact resultDominance
  · intro dominatorIndex semanticIDom
    have hstrict := immediateDominator_index_lt ordered blockIndex dominatorIndex semanticIDom
    have dominates :
        (reversePostOrder.get dominatorIndex).DominatesInSSACFGRegion
          (reversePostOrder.get blockIndex) region irCtx :=
      Or.inr semanticIDom.1
    obtain ⟨semanticResult, hsemanticResult, _, resultDominance⟩ :=
      forest.intersect_preserves_dominator ordered dominatorIndex candidate1 candidate2
        first.initialized second.initialized
        (first.preserves_strict_dominators dominatorIndex hstrict dominates)
        (second.preserves_strict_dominators dominatorIndex hstrict dominates)
    have heq : semanticResult = result := by
      apply Fin.eq_of_val_eq
      exact hsemanticResult.symm.trans hresult
    subst semanticResult
    exact ordered dominatorIndex result resultDominance

/-- Once a partial fold is earlier than the block, it is a valid update candidate. -/
theorem PartialCandidateForBlock.toUpdateCandidate [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    {blockIndex immediateDominator : Fin blockCount}
    (candidate : PartialCandidateForBlock value reversePostOrder region irCtx
      blockIndex immediateDominator)
    (decreases : immediateDominator < blockIndex) :
    UpdateCandidateForBlock value reversePostOrder region irCtx
      blockIndex immediateDominator :=
  { candidate with decreases := Or.inr decreases }

/-- Intersecting a valid update candidate with another partial candidate remains valid. -/
theorem UpdateCandidateForBlock.intersect [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (ordered : OrderedForRegion reversePostOrder region irCtx)
    (blockIndex candidate1 candidate2 : Fin blockCount)
    (first : UpdateCandidateForBlock value reversePostOrder region irCtx
      blockIndex candidate1)
    (second : PartialCandidateForBlock value reversePostOrder region irCtx
      blockIndex candidate2)
    (blockIsNotEntry : blockIndex.val ≠ 0) :
    ∃ result : Fin blockCount,
      value.intersect candidate1.val candidate2.val = result.val ∧
        UpdateCandidateForBlock value reversePostOrder region irCtx blockIndex result := by
  obtain ⟨result, hresult, partialCandidate⟩ :=
    first.toPartialCandidateForBlock.intersect forest ordered blockIndex candidate1 candidate2
      second
  have hle := forest.intersect_le_inputs candidate1 candidate2
    first.initialized second.initialized |>.1
  have firstDecreases : candidate1 < blockIndex := by
    rcases first.decreases with hentry | hdecreases
    · exact False.elim (blockIsNotEntry hentry.1)
    · exact hdecreases
  have resultDecreases : result < blockIndex := by
    rw [hresult] at hle
    exact Nat.lt_of_le_of_lt hle firstDecreases
  exact ⟨result, hresult, partialCandidate.toUpdateCandidate resultDecreases⟩

/-- A predecessor fold only observes working-parent entries below its RPO boundary. -/
private theorem fold_predecessors_eq_of_agree_below
    (value1 value2 : DominanceValue blockCount)
    (bound : Nat)
    (predecessors : Array Nat)
    (agrees : ∀ index, index < bound → value1.get! index = value2.get! index)
    (parentBefore : ∀ index, index < bound → value1.get! index < bound)
    (parentDecreases : ∀ index, 0 < index → index < bound → value1.get! index < index)
    (predecessorsBefore : ∀ predecessorIndex ∈ predecessors, predecessorIndex < bound) :
    predecessors.foldl (DominanceAnalysis.predecessorStep value1) (none, false) =
      predecessors.foldl (DominanceAnalysis.predecessorStep value2) (none, false) := by
  have go : ∀ (indices : List Nat) (state : Option Nat × Bool),
      CandidateBefore state.1 bound →
      (∀ predecessorIndex ∈ indices, predecessorIndex < bound) →
      indices.foldl (DominanceAnalysis.predecessorStep value1) state =
          indices.foldl (DominanceAnalysis.predecessorStep value2) state ∧
        CandidateBefore
          (indices.foldl (DominanceAnalysis.predecessorStep value1) state).1 bound := by
    intro indices
    induction indices with
    | nil =>
        intro state candidateBefore _
        exact ⟨rfl, candidateBefore⟩
    | cons predecessorIndex remaining ih =>
        intro state candidateBefore indicesBefore
        have predecessorBefore : predecessorIndex < bound :=
          indicesBefore predecessorIndex (by simp)
        have stepEq :
            DominanceAnalysis.predecessorStep value1 state predecessorIndex =
              DominanceAnalysis.predecessorStep value2 state predecessorIndex := by
          unfold DominanceAnalysis.predecessorStep
          rw [agrees predecessorIndex predecessorBefore]
          by_cases unknown : value2.get! predecessorIndex = blockCount
          · simp only [unknown, ↓reduceIte]
          · simp only [unknown, ↓reduceIte]
            rcases candidateBefore with hnone | ⟨candidateIndex, hcandidate, hbefore⟩
            · simp only [hnone]
            · simp only [hcandidate]
              rw [intersect_eq_of_agree_below value1 value2 bound predecessorIndex
                candidateIndex agrees parentDecreases predecessorBefore hbefore]
        have nextCandidateBefore : CandidateBefore
            (DominanceAnalysis.predecessorStep value1 state predecessorIndex).1 bound := by
          unfold DominanceAnalysis.predecessorStep
          by_cases unknown : value1.get! predecessorIndex = blockCount
          · simp only [unknown, ↓reduceIte]
            exact candidateBefore
          · simp only [unknown, ↓reduceIte]
            rcases candidateBefore with hnone | ⟨candidateIndex, hcandidate, hbefore⟩
            · simp only [hnone]
              exact Or.inr ⟨predecessorIndex, rfl, predecessorBefore⟩
            · simp only [hcandidate]
              refine Or.inr ⟨value1.intersect predecessorIndex candidateIndex, rfl, ?_⟩
              exact intersect_preserves value1 (fun index => index < bound) parentBefore
                predecessorBefore hbefore
        simp only [List.foldl]
        have tail := ih
          (DominanceAnalysis.predecessorStep value1 state predecessorIndex)
          nextCandidateBefore
          (fun queriedIndex hmem =>
            indicesBefore queriedIndex (List.mem_cons_of_mem predecessorIndex hmem))
        rw [← stepEq]
        exact tail
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact (go predecessors.toList (none, false) (Or.inl rfl)
    (fun predecessorIndex hmem => predecessorsBefore predecessorIndex (by simpa using hmem))).1

/-- Once a predecessor fold starts waiting, later steps cannot clear the flag. -/
private theorem fold_predecessors_waiting_true
    (value : DominanceValue blockCount)
    (predecessors : Array Nat)
    (candidate : Option Nat) :
    (predecessors.foldl
      (DominanceAnalysis.predecessorStep value) (candidate, true)).2 = true := by
  have go : ∀ (indices : List Nat) (candidate : Option Nat),
      (indices.foldl
        (DominanceAnalysis.predecessorStep value) (candidate, true)).2 = true := by
    intro indices
    induction indices with
    | nil => simp
    | cons predecessorIndex remaining ih =>
        intro candidate
        simp only [List.foldl]
        unfold DominanceAnalysis.predecessorStep
        split
        · exact ih candidate
        · exact ih _
  rw [← Array.foldl_toList]
  exact go predecessors.toList candidate

/-- A non-waiting predecessor fold saw an initialized value at every index. -/
private theorem predecessor_known_of_fold_waiting_false
    (value : DominanceValue blockCount)
    (predecessors : Array Nat)
    (notWaiting : (predecessors.foldl
      (DominanceAnalysis.predecessorStep value) (none, false)).2 = false) :
    ∀ predecessorIndex ∈ predecessors,
      value.get! predecessorIndex ≠ blockCount := by
  have go : ∀ (indices : List Nat) (candidate : Option Nat),
      (indices.foldl
        (DominanceAnalysis.predecessorStep value) (candidate, false)).2 = false →
      ∀ predecessorIndex ∈ indices, value.get! predecessorIndex ≠ blockCount := by
    intro indices
    induction indices with
    | nil => simp
    | cons current remaining ih =>
        intro candidate folded predecessorIndex hmem
        simp only [List.foldl] at folded
        by_cases unknown : value.get! current = blockCount
        · have currentStep :
              DominanceAnalysis.predecessorStep value (candidate, false) current =
                (candidate, true) := by
            simp [DominanceAnalysis.predecessorStep, unknown]
          rw [currentStep] at folded
          have waitingTrue := fold_predecessors_waiting_true value remaining.toArray candidate
          have waitingTrueList : (remaining.foldl
              (DominanceAnalysis.predecessorStep value) (candidate, true)).2 = true := by
            simpa [Array.foldl_toList] using waitingTrue
          rw [waitingTrueList] at folded
          contradiction
        · let nextCandidate := some (match candidate with
              | none => current
              | some candidateIndex => value.intersect current candidateIndex)
          have currentStep :
              DominanceAnalysis.predecessorStep value (candidate, false) current =
                (nextCandidate, false) := by
            simp only [DominanceAnalysis.predecessorStep, unknown, ↓reduceIte,
              nextCandidate]
            rfl
          rw [currentStep] at folded
          rcases List.mem_cons.mp hmem with currentEq | remainingMem
          · subst predecessorIndex
            exact unknown
          · exact ih nextCandidate folded predecessorIndex remainingMem
  rw [← Array.foldl_toList] at notWaiting
  intro predecessorIndex hmem
  exact go predecessors.toList none notWaiting predecessorIndex (by simpa using hmem)

/-- Every working-parent lookup below a non-entry boundary remains below that boundary. -/
private theorem WorkingForestForRegion.parent_before_boundary [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (blockIndex : Fin blockCount)
    (_blockIsNotEntry : blockIndex.val ≠ 0)
    (initializedBefore : InitializedBefore value blockIndex) :
    ∀ index, index < blockIndex.val → value.get! index < blockIndex.val := by
  intro index indexBefore
  let indexFin : Fin blockCount := ⟨index, Nat.lt_trans indexBefore blockIndex.isLt⟩
  obtain ⟨parentIndex, parentEq⟩ := initializedBefore indexFin indexBefore
  have encodedParent := get!_eq_of_get?_eq_some value indexFin parentIndex parentEq
  rw [encodedParent]
  rcases forest.parent_decreases indexFin parentIndex parentEq with entry | decreases
  · simp only [indexFin] at entry
    omega
  · exact Nat.lt_trans decreases indexBefore

/-- Positive working-parent lookups strictly decrease below an RPO boundary. -/
private theorem WorkingForestForRegion.parent_decreases_before [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (blockIndex : Fin blockCount)
    (initializedBefore : InitializedBefore value blockIndex) :
    ∀ index, 0 < index → index < blockIndex.val → value.get! index < index := by
  intro index indexPositive indexBefore
  let indexFin : Fin blockCount := ⟨index, Nat.lt_trans indexBefore blockIndex.isLt⟩
  obtain ⟨parentIndex, parentEq⟩ := initializedBefore indexFin indexBefore
  have encodedParent := get!_eq_of_get?_eq_some value indexFin parentIndex parentEq
  rw [encodedParent]
  rcases forest.parent_decreases indexFin parentIndex parentEq with entry | decreases
  · simp only [indexFin] at entry
    omega
  · exact decreases

/-- If the initial sweep is not waiting, every predecessor was already earlier in RPO. -/
theorem RegionMetadataForRegion.predecessors_before_of_not_waiting [HasOpInfo OpInfo]
    [NeZero blockCount]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (blockIndex : Fin blockCount)
    (blockIsNotEntry : blockIndex.val ≠ 0)
    (uninitializedFrom : UninitializedFrom value blockIndex.val)
    (notWaiting : (DominanceAnalysis.computeImmediateDominator
      blockIndex.val predecessors value).2 = false) :
    ∀ predecessorIndex ∈ predecessors[blockIndex.val]!,
      predecessorIndex < blockIndex.val := by
  unfold DominanceAnalysis.computeImmediateDominator at notWaiting
  simp only [blockIsNotEntry, ↓reduceIte] at notWaiting
  have known := predecessor_known_of_fold_waiting_false value
    predecessors[blockIndex.val]! notWaiting
  intro predecessorIndex predecessorMem
  obtain ⟨representedPredecessor, predecessorEq, _, _⟩ :=
    metadata.predecessors_sound blockIndex predecessorIndex predecessorMem
  by_cases before : predecessorIndex < blockIndex.val
  · exact before
  · have sentinel := uninitializedFrom representedPredecessor (by
      rw [predecessorEq]
      omega)
    exact False.elim
      (known predecessorIndex predecessorMem (by simpa [predecessorEq] using sentinel))

/-- Computing an earlier block is unchanged by refinements at later RPO indices. -/
theorem WorkingForestForRegion.compute_eq_of_agreesBefore [HasOpInfo OpInfo]
    {value1 value2 : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value1 reversePostOrder region irCtx)
    (blockIndex : Fin blockCount)
    (blockIsNotEntry : blockIndex.val ≠ 0)
    (initializedBefore : InitializedBefore value1 blockIndex)
    (predecessors : Array (Array Nat))
    (predecessorsBefore : ∀ predecessorIndex ∈ predecessors[blockIndex.val]!,
      predecessorIndex < blockIndex.val)
    (agrees : AgreesBefore value1 value2 blockIndex.val) :
    DominanceAnalysis.computeImmediateDominator blockIndex.val predecessors value1 =
      DominanceAnalysis.computeImmediateDominator blockIndex.val predecessors value2 := by
  unfold DominanceAnalysis.computeImmediateDominator
  simp only [blockIsNotEntry, ↓reduceIte]
  apply fold_predecessors_eq_of_agree_below value1 value2 blockIndex.val
  · intro index indexBefore
    let indexFin : Fin blockCount := ⟨index, Nat.lt_trans indexBefore blockIndex.isLt⟩
    exact agrees indexFin indexBefore
  · exact forest.parent_before_boundary blockIndex blockIsNotEntry initializedBefore
  · exact forest.parent_decreases_before blockIndex initializedBefore
  · exact predecessorsBefore

/-- One executable predecessor step preserves a sound optional candidate. -/
theorem CandidateStateForBlock.predecessorStep [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (injectiveRPO : InjectiveRPO reversePostOrder)
    (ordered : OrderedForRegion reversePostOrder region irCtx)
    (blockIndex : Fin blockCount)
    (candidate : Option Nat)
    (waiting : Bool)
    (predecessorIndex : Nat)
    (candidateSound : CandidateStateForBlock value reversePostOrder region irCtx
      blockIndex candidate)
    (predecessorSound : PredecessorIndexForBlock reversePostOrder region irCtx
      blockIndex predecessorIndex) :
    CandidateStateForBlock value reversePostOrder region irCtx blockIndex
      (DominanceAnalysis.predecessorStep value (candidate, waiting) predecessorIndex).1 := by
  obtain ⟨predecessor, hpredecessor, predecessorParent, edge⟩ := predecessorSound
  subst predecessorIndex
  unfold DominanceAnalysis.predecessorStep
  by_cases huninitialized : value.get! predecessor.val = blockCount
  · simp only [huninitialized, ↓reduceIte]
    exact candidateSound
  · simp only [huninitialized, ↓reduceIte]
    have hlt : value.get! predecessor.val < blockCount := by
      have hle := get!_le_blockCount value predecessor
      omega
    let predecessorParentIndex : Fin blockCount := ⟨value.get! predecessor.val, hlt⟩
    have predecessorInitialized : Initialized value predecessor := by
      refine ⟨predecessorParentIndex, ?_⟩
      exact get?_eq_some_get! value forest.not_bottom predecessor hlt
    have predecessorCandidate := PartialCandidateForBlock.of_predecessor
      injectiveRPO ordered blockIndex predecessor predecessorParent edge predecessorInitialized
    rcases candidateSound with hnone | ⟨oldCandidate, hold, oldCandidateSound⟩
    · exact Or.inr ⟨predecessor, by simp only [hnone], predecessorCandidate⟩
    · obtain ⟨result, hresult, resultSound⟩ :=
        predecessorCandidate.intersect forest ordered blockIndex predecessor oldCandidate
          oldCandidateSound
      right
      refine ⟨result, ?_, resultSound⟩
      simp only [hold]
      exact congrArg some hresult

/-- Folding `predecessorStep` over sound predecessor indices preserves candidate soundness. -/
theorem CandidateStateForBlock.fold_predecessors [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (injectiveRPO : InjectiveRPO reversePostOrder)
    (ordered : OrderedForRegion reversePostOrder region irCtx)
    (blockIndex : Fin blockCount)
    (predecessors : Array Nat)
    (predecessorsSound : ∀ predecessorIndex ∈ predecessors,
      PredecessorIndexForBlock reversePostOrder region irCtx
        blockIndex predecessorIndex) :
    CandidateStateForBlock value reversePostOrder region irCtx blockIndex
      (predecessors.foldl (DominanceAnalysis.predecessorStep value) (none, false)).1 := by
  have foldPreserves : ∀ (indices : List Nat) (state : Option Nat × Bool),
      (∀ predecessorIndex ∈ indices,
        PredecessorIndexForBlock reversePostOrder region irCtx
          blockIndex predecessorIndex) →
      CandidateStateForBlock value reversePostOrder region irCtx blockIndex state.1 →
      CandidateStateForBlock value reversePostOrder region irCtx blockIndex
        (indices.foldl (DominanceAnalysis.predecessorStep value) state).1 := by
    intro indices
    induction indices with
    | nil =>
        intro state _ stateSound
        exact stateSound
    | cons predecessorIndex remaining ih =>
        intro state indicesSound stateSound
        simp only [List.foldl]
        apply ih
        · intro queriedIndex hmem
          exact indicesSound queriedIndex (List.mem_cons_of_mem predecessorIndex hmem)
        · exact stateSound.predecessorStep forest injectiveRPO ordered blockIndex
            state.1 state.2 predecessorIndex (indicesSound predecessorIndex (by simp))
  rw [← Array.foldl_toList]
  apply foldPreserves predecessors.toList (none, false)
  · intro predecessorIndex hmem
    exact predecessorsSound predecessorIndex (by simpa using hmem)
  · exact Or.inl rfl

/-- Once established, an upper bound survives every subsequent predecessor step. -/
theorem CandidateBoundedBy.predecessorStep [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (upperBound : Fin blockCount)
    (candidate : Option Nat)
    (waiting : Bool)
    (predecessorIndex : Nat)
    (bounded : CandidateBoundedBy value upperBound candidate)
    (predecessorSound : PredecessorIndexForBlock reversePostOrder region irCtx
      blockIndex predecessorIndex) :
    CandidateBoundedBy value upperBound
      (DominanceAnalysis.predecessorStep value (candidate, waiting) predecessorIndex).1 := by
  obtain ⟨predecessor, hpredecessor, _, _⟩ := predecessorSound
  subst predecessorIndex
  unfold DominanceAnalysis.predecessorStep
  by_cases huninitialized : value.get! predecessor.val = blockCount
  · simp only [huninitialized, ↓reduceIte]
    exact bounded
  · simp only [huninitialized, ↓reduceIte]
    have hlt : value.get! predecessor.val < blockCount := by
      have hle := get!_le_blockCount value predecessor
      omega
    let predecessorParentIndex : Fin blockCount := ⟨value.get! predecessor.val, hlt⟩
    have predecessorInitialized : Initialized value predecessor := by
      refine ⟨predecessorParentIndex, ?_⟩
      exact get?_eq_some_get! value forest.not_bottom predecessor hlt
    obtain ⟨oldCandidate, hold, oldInitialized, oldBound⟩ := bounded
    obtain ⟨result, hresult, resultInitialized⟩ :=
      forest.intersect_initialized predecessor oldCandidate predecessorInitialized oldInitialized
    refine ⟨result, ?_, resultInitialized, ?_⟩
    · simp only [hold]
      exact congrArg some hresult
    · have hle := forest.intersect_le_inputs predecessor oldCandidate
        predecessorInitialized oldInitialized |>.2
      rw [hresult] at hle
      exact Nat.le_trans hle oldBound

/-- Processing an initialized index establishes that index as an upper bound. -/
theorem CandidateStateForBlock.predecessorStep_self_bounded [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (blockIndex predecessor : Fin blockCount)
    (candidate : Option Nat)
    (waiting : Bool)
    (candidateSound : CandidateStateForBlock value reversePostOrder region irCtx
      blockIndex candidate)
    (predecessorInitialized : Initialized value predecessor) :
    CandidateBoundedBy value predecessor
      (DominanceAnalysis.predecessorStep value (candidate, waiting) predecessor.val).1 := by
  have predecessorStillInitialized := predecessorInitialized
  obtain ⟨predecessorParent, hget⟩ := predecessorInitialized
  have hencoded := get!_eq_of_get?_eq_some value predecessor predecessorParent hget
  have hinitialized : value.get! predecessor.val ≠ blockCount := by
    rw [hencoded]
    exact Nat.ne_of_lt predecessorParent.isLt
  unfold DominanceAnalysis.predecessorStep
  simp only [hinitialized, ↓reduceIte]
  rcases candidateSound with hnone | ⟨oldCandidate, hold, oldCandidateSound⟩
  · exact ⟨predecessor, by simp only [hnone], predecessorStillInitialized, Nat.le_refl _⟩
  · obtain ⟨result, hresult, resultInitialized⟩ :=
      forest.intersect_initialized predecessor oldCandidate predecessorStillInitialized
        oldCandidateSound.initialized
    refine ⟨result, ?_, resultInitialized, ?_⟩
    · simp only [hold]
      exact congrArg some hresult
    · have hle := forest.intersect_le_inputs predecessor oldCandidate
        predecessorStillInitialized oldCandidateSound.initialized |>.1
      rwa [hresult] at hle

/-- The final fold result is bounded by every initialized predecessor it processed. -/
theorem CandidateStateForBlock.fold_predecessors_bounded [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (injectiveRPO : InjectiveRPO reversePostOrder)
    (ordered : OrderedForRegion reversePostOrder region irCtx)
    (blockIndex upperBound : Fin blockCount)
    (predecessors : Array Nat)
    (predecessorsSound : ∀ predecessorIndex ∈ predecessors,
      PredecessorIndexForBlock reversePostOrder region irCtx
        blockIndex predecessorIndex)
    (upperBoundMem : upperBound.val ∈ predecessors)
    (upperBoundInitialized : Initialized value upperBound) :
    CandidateBoundedBy value upperBound
      (predecessors.foldl (DominanceAnalysis.predecessorStep value) (none, false)).1 := by
  have foldFrom : ∀ (indices : List Nat) (state : Option Nat × Bool),
      (∀ predecessorIndex ∈ indices,
        PredecessorIndexForBlock reversePostOrder region irCtx
          blockIndex predecessorIndex) →
      CandidateStateForBlock value reversePostOrder region irCtx blockIndex state.1 →
      (CandidateBoundedBy value upperBound state.1 ∨ upperBound.val ∈ indices) →
      CandidateBoundedBy value upperBound
        (indices.foldl (DominanceAnalysis.predecessorStep value) state).1 := by
    intro indices
    induction indices with
    | nil =>
        intro state _ _ progress
        exact progress.resolve_right (by simp)
    | cons predecessorIndex remaining ih =>
        intro state indicesSound stateSound progress
        simp only [List.foldl]
        have predecessorSound := indicesSound predecessorIndex (by simp)
        have nextStateSound := stateSound.predecessorStep forest injectiveRPO ordered
          blockIndex state.1 state.2 predecessorIndex predecessorSound
        apply ih _ (fun queriedIndex hmem =>
          indicesSound queriedIndex (List.mem_cons_of_mem predecessorIndex hmem)) nextStateSound
        rcases progress with alreadyBounded | upperBoundPending
        · left
          exact alreadyBounded.predecessorStep forest upperBound state.1 state.2
            predecessorIndex predecessorSound
        · rcases List.mem_cons.mp upperBoundPending with hcurrent | hremaining
          · left
            subst predecessorIndex
            exact stateSound.predecessorStep_self_bounded forest blockIndex upperBound
              state.1 state.2 upperBoundInitialized
          · exact Or.inr hremaining
  rw [← Array.foldl_toList]
  apply foldFrom predecessors.toList (none, false)
  · intro predecessorIndex hmem
    exact predecessorsSound predecessorIndex (by simpa using hmem)
  · exact Or.inl rfl
  · exact Or.inr (by simpa using upperBoundMem)

/-- A predecessor step preserves ancestry already established by the fold candidate. -/
theorem CandidateAncestorOf.predecessorStep [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (blockIndex predecessor : Fin blockCount)
    (candidate : Option Nat)
    (waiting : Bool)
    (candidateSound : CandidateStateForBlock value reversePostOrder region irCtx
      blockIndex candidate)
    (predecessorInitialized : Initialized value predecessor)
    (targetIndex : Nat)
    (ancestor : CandidateAncestorOf value targetIndex candidate) :
    CandidateAncestorOf value targetIndex
      (DominanceAnalysis.predecessorStep value
        (candidate, waiting) predecessor.val).1 := by
  have predecessorStillInitialized := predecessorInitialized
  obtain ⟨predecessorParent, hpredecessor⟩ := predecessorInitialized
  have hencoded := get!_eq_of_get?_eq_some value predecessor predecessorParent hpredecessor
  have hinitialized : value.get! predecessor.val ≠ blockCount := by
    rw [hencoded]
    exact Nat.ne_of_lt predecessorParent.isLt
  unfold DominanceAnalysis.predecessorStep
  simp only [hinitialized, ↓reduceIte]
  rcases candidateSound with hnone | ⟨oldCandidate, hold, oldCandidateSound⟩
  · obtain ⟨ancestorIndex, hcandidate, _⟩ := ancestor
    rw [hnone] at hcandidate
    contradiction
  · obtain ⟨ancestorIndex, hcandidate, hancestor⟩ := ancestor
    have hancestorIndex : ancestorIndex = oldCandidate.val := by
      rw [hold] at hcandidate
      exact Option.some.inj hcandidate |>.symm
    subst ancestorIndex
    obtain ⟨_, intersectAncestor⟩ :=
      forest.intersect_ancestor_inputs predecessor oldCandidate predecessorStillInitialized
        oldCandidateSound.initialized
    refine ⟨value.intersect predecessor.val oldCandidate.val, ?_, ?_⟩
    · simp only [hold]
    · exact intersectAncestor.trans hancestor

/-- Processing a predecessor makes the candidate a working ancestor of that predecessor. -/
theorem CandidateStateForBlock.predecessorStep_self_ancestor [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (blockIndex predecessor : Fin blockCount)
    (candidate : Option Nat)
    (waiting : Bool)
    (candidateSound : CandidateStateForBlock value reversePostOrder region irCtx
      blockIndex candidate)
    (predecessorInitialized : Initialized value predecessor) :
    CandidateAncestorOf value predecessor.val
      (DominanceAnalysis.predecessorStep value
        (candidate, waiting) predecessor.val).1 := by
  have predecessorStillInitialized := predecessorInitialized
  obtain ⟨predecessorParent, hpredecessor⟩ := predecessorInitialized
  have hencoded := get!_eq_of_get?_eq_some value predecessor predecessorParent hpredecessor
  have hinitialized : value.get! predecessor.val ≠ blockCount := by
    rw [hencoded]
    exact Nat.ne_of_lt predecessorParent.isLt
  unfold DominanceAnalysis.predecessorStep
  simp only [hinitialized, ↓reduceIte]
  rcases candidateSound with hnone | ⟨oldCandidate, hold, oldCandidateSound⟩
  · refine ⟨predecessor.val, ?_, WorkingAncestor.refl predecessor.val⟩
    simp only [hnone]
  · obtain ⟨intersectAncestor, _⟩ :=
      forest.intersect_ancestor_inputs predecessor oldCandidate predecessorStillInitialized
        oldCandidateSound.initialized
    refine ⟨value.intersect predecessor.val oldCandidate.val, ?_, intersectAncestor⟩
    simp only [hold]

/-- The final fold candidate is a working ancestor of every predecessor it processed. -/
theorem CandidateStateForBlock.fold_predecessors_ancestor [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (injectiveRPO : InjectiveRPO reversePostOrder)
    (ordered : OrderedForRegion reversePostOrder region irCtx)
    (blockIndex : Fin blockCount)
    (predecessors : Array Nat)
    (predecessorsSound : ∀ predecessorIndex ∈ predecessors,
      PredecessorIndexForBlock reversePostOrder region irCtx
        blockIndex predecessorIndex)
    (allInitialized : ∀ predecessorIndex ∈ predecessors,
      ∃ predecessor : Fin blockCount,
        predecessor.val = predecessorIndex ∧ Initialized value predecessor)
    (targetIndex : Nat)
    (targetMem : targetIndex ∈ predecessors) :
    CandidateAncestorOf value targetIndex
      (predecessors.foldl
        (DominanceAnalysis.predecessorStep value) (none, false)).1 := by
  have foldFrom : ∀ (indices : List Nat) (state : Option Nat × Bool),
      (∀ predecessorIndex ∈ indices,
        PredecessorIndexForBlock reversePostOrder region irCtx
          blockIndex predecessorIndex) →
      (∀ predecessorIndex ∈ indices,
        ∃ predecessor : Fin blockCount,
          predecessor.val = predecessorIndex ∧ Initialized value predecessor) →
      CandidateStateForBlock value reversePostOrder region irCtx blockIndex state.1 →
      (CandidateAncestorOf value targetIndex state.1 ∨ targetIndex ∈ indices) →
      CandidateAncestorOf value targetIndex
        (indices.foldl (DominanceAnalysis.predecessorStep value) state).1 := by
    intro indices
    induction indices with
    | nil =>
        intro state _ _ _ progress
        exact progress.resolve_right (by simp)
    | cons predecessorIndex remaining ih =>
        intro state indicesSound indicesInitialized stateSound progress
        simp only [List.foldl]
        have predecessorSound := indicesSound predecessorIndex (by simp)
        obtain ⟨predecessor, hpredecessor, predecessorInitialized⟩ :=
          indicesInitialized predecessorIndex (by simp)
        subst predecessorIndex
        have nextStateSound := stateSound.predecessorStep forest injectiveRPO ordered
          blockIndex state.1 state.2 predecessor.val predecessorSound
        apply ih _
          (fun queriedIndex hmem =>
            indicesSound queriedIndex (List.mem_cons_of_mem predecessor.val hmem))
          (fun queriedIndex hmem =>
            indicesInitialized queriedIndex (List.mem_cons_of_mem predecessor.val hmem))
          nextStateSound
        rcases progress with alreadyAncestor | targetPending
        · left
          exact alreadyAncestor.predecessorStep forest blockIndex predecessor state.1 state.2
            stateSound predecessorInitialized targetIndex
        · rcases List.mem_cons.mp targetPending with hcurrent | hremaining
          · left
            subst targetIndex
            exact stateSound.predecessorStep_self_ancestor forest blockIndex predecessor
              state.1 state.2 predecessorInitialized
          · exact Or.inr hremaining
  rw [← Array.foldl_toList]
  apply foldFrom predecessors.toList (none, false)
  · intro predecessorIndex hmem
    exact predecessorsSound predecessorIndex (by simpa using hmem)
  · intro predecessorIndex hmem
    exact allInitialized predecessorIndex (by simpa using hmem)
  · exact Or.inl rfl
  · exact Or.inr (by simpa using targetMem)

/-- A non-entry candidate returned by the executable fold is a sound partial candidate. -/
theorem computeImmediateDominator_partial [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (injectiveRPO : InjectiveRPO reversePostOrder)
    (ordered : OrderedForRegion reversePostOrder region irCtx)
    (blockIndex : Fin blockCount)
    (blockIsNotEntry : blockIndex.val ≠ 0)
    (predecessors : Array (Array Nat))
    (predecessorsSound : ∀ predecessorIndex ∈ predecessors[blockIndex.val]!,
      PredecessorIndexForBlock reversePostOrder region irCtx
        blockIndex predecessorIndex)
    (candidateIndex : Nat)
    (waiting : Bool)
    (hcompute : DominanceAnalysis.computeImmediateDominator
      blockIndex.val predecessors value = (some candidateIndex, waiting)) :
    ∃ candidate : Fin blockCount,
      candidateIndex = candidate.val ∧
        PartialCandidateForBlock value reversePostOrder region irCtx
          blockIndex candidate := by
  have candidateState := CandidateStateForBlock.fold_predecessors
    forest injectiveRPO ordered blockIndex predecessors[blockIndex.val]! predecessorsSound
  unfold DominanceAnalysis.computeImmediateDominator at hcompute
  simp only [blockIsNotEntry, ↓reduceIte] at hcompute
  have hcandidates := congrArg Prod.fst hcompute
  rcases candidateState with hnone | ⟨candidate, hcandidate, candidateSound⟩
  · rw [hnone] at hcandidates
    contradiction
  · rw [hcandidate] at hcandidates
    exact ⟨candidate, Option.some.inj hcandidates |>.symm, candidateSound⟩

/-- Seeing an initialized earlier predecessor makes the executable candidate decrease. -/
theorem computeImmediateDominator_decreases [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (injectiveRPO : InjectiveRPO reversePostOrder)
    (ordered : OrderedForRegion reversePostOrder region irCtx)
    (blockIndex earlierPredecessor : Fin blockCount)
    (blockIsNotEntry : blockIndex.val ≠ 0)
    (earlier : earlierPredecessor < blockIndex)
    (earlierInitialized : Initialized value earlierPredecessor)
    (predecessors : Array (Array Nat))
    (predecessorsSound : ∀ predecessorIndex ∈ predecessors[blockIndex.val]!,
      PredecessorIndexForBlock reversePostOrder region irCtx
        blockIndex predecessorIndex)
    (earlierMem : earlierPredecessor.val ∈ predecessors[blockIndex.val]!)
    (candidateIndex : Nat)
    (waiting : Bool)
    (hcompute : DominanceAnalysis.computeImmediateDominator
      blockIndex.val predecessors value = (some candidateIndex, waiting)) :
    candidateIndex < blockIndex.val := by
  have bounded := CandidateStateForBlock.fold_predecessors_bounded
    forest injectiveRPO ordered blockIndex earlierPredecessor
      predecessors[blockIndex.val]! predecessorsSound earlierMem earlierInitialized
  unfold DominanceAnalysis.computeImmediateDominator at hcompute
  simp only [blockIsNotEntry, ↓reduceIte] at hcompute
  have hcandidates := congrArg Prod.fst hcompute
  obtain ⟨candidate, hcandidate, _, candidateBound⟩ := bounded
  rw [hcandidate] at hcandidates
  have heq := Option.some.inj hcandidates
  omega

/--
Updating a non-entry block with the executable predecessor-fold result preserves
the working forest and semantic soundness, provided the result is earlier in RPO.
-/
theorem computeImmediateDominator_refine_preserves [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (sound : SoundForRegion value reversePostOrder region irCtx)
    (injectiveRPO : InjectiveRPO reversePostOrder)
    (ordered : OrderedForRegion reversePostOrder region irCtx)
    (blockIndex : Fin blockCount)
    (blockIsNotEntry : blockIndex.val ≠ 0)
    (predecessors : Array (Array Nat))
    (predecessorsSound : ∀ predecessorIndex ∈ predecessors[blockIndex.val]!,
      PredecessorIndexForBlock reversePostOrder region irCtx
        blockIndex predecessorIndex)
    (candidateIndex : Nat)
    (waiting : Bool)
    (hcompute : DominanceAnalysis.computeImmediateDominator
      blockIndex.val predecessors value = (some candidateIndex, waiting))
    (candidateDecreases : candidateIndex < blockIndex.val) :
    WorkingForestForRegion
        (value.refine! blockIndex.val candidateIndex)
        reversePostOrder region irCtx ∧
      SoundForRegion
        (value.refine! blockIndex.val candidateIndex)
        reversePostOrder region irCtx := by
  obtain ⟨candidate, hcandidate, partialCandidate⟩ :=
    computeImmediateDominator_partial forest injectiveRPO ordered blockIndex
      blockIsNotEntry predecessors predecessorsSound candidateIndex waiting hcompute
  subst candidateIndex
  have updateCandidate := partialCandidate.toUpdateCandidate candidateDecreases
  exact refine_preserves_invariants forest sound blockIndex candidate updateCandidate

/--
An executable non-entry update preserves both invariants once the RPO sweep has
processed one earlier predecessor of the block.
-/
theorem computeImmediateDominator_refine_preserves_of_earlier_predecessor
    [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (sound : SoundForRegion value reversePostOrder region irCtx)
    (injectiveRPO : InjectiveRPO reversePostOrder)
    (ordered : OrderedForRegion reversePostOrder region irCtx)
    (blockIndex earlierPredecessor : Fin blockCount)
    (blockIsNotEntry : blockIndex.val ≠ 0)
    (earlier : earlierPredecessor < blockIndex)
    (earlierInitialized : Initialized value earlierPredecessor)
    (predecessors : Array (Array Nat))
    (predecessorsSound : ∀ predecessorIndex ∈ predecessors[blockIndex.val]!,
      PredecessorIndexForBlock reversePostOrder region irCtx
        blockIndex predecessorIndex)
    (earlierMem : earlierPredecessor.val ∈ predecessors[blockIndex.val]!)
    (candidateIndex : Nat)
    (waiting : Bool)
    (hcompute : DominanceAnalysis.computeImmediateDominator
      blockIndex.val predecessors value = (some candidateIndex, waiting)) :
    WorkingForestForRegion
        (value.refine! blockIndex.val candidateIndex)
        reversePostOrder region irCtx ∧
      SoundForRegion
        (value.refine! blockIndex.val candidateIndex)
        reversePostOrder region irCtx := by
  have candidateDecreases := computeImmediateDominator_decreases forest injectiveRPO ordered
    blockIndex earlierPredecessor blockIsNotEntry earlier earlierInitialized predecessors
    predecessorsSound earlierMem candidateIndex waiting hcompute
  exact computeImmediateDominator_refine_preserves forest sound injectiveRPO ordered
    blockIndex blockIsNotEntry predecessors predecessorsSound candidateIndex waiting hcompute
    candidateDecreases

/--
The metadata contract discharges every side condition for a non-entry CHK block
update once the preceding RPO prefix has been initialized.
-/
theorem RegionMetadataForRegion.compute_refine_preserves [HasOpInfo OpInfo]
    [NeZero blockCount]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (sound : SoundForRegion value reversePostOrder region irCtx)
    (blockIndex : Fin blockCount)
    (blockIsNotEntry : blockIndex.val ≠ 0)
    (initializedBefore : InitializedBefore value blockIndex)
    (candidateIndex : Nat)
    (waiting : Bool)
    (hcompute : DominanceAnalysis.computeImmediateDominator
      blockIndex.val predecessors value = (some candidateIndex, waiting)) :
    WorkingForestForRegion
        (value.refine! blockIndex.val candidateIndex)
        reversePostOrder region irCtx ∧
      SoundForRegion
        (value.refine! blockIndex.val candidateIndex)
        reversePostOrder region irCtx ∧
      Initialized
        (value.refine! blockIndex.val candidateIndex) blockIndex := by
  let ordered := metadata.orderedForRegion
  obtain ⟨earlierPredecessor, earlier, earlierMem⟩ :=
    metadata.earlier_predecessor blockIndex blockIsNotEntry
  have earlierInitialized := initializedBefore earlierPredecessor earlier
  have invariants := computeImmediateDominator_refine_preserves_of_earlier_predecessor
    forest sound metadata.injective_rpo ordered blockIndex earlierPredecessor blockIsNotEntry
    earlier earlierInitialized predecessors (metadata.predecessors_sound blockIndex) earlierMem
    candidateIndex waiting hcompute
  obtain ⟨candidate, hcandidate, _⟩ :=
    computeImmediateDominator_partial forest metadata.injective_rpo ordered blockIndex
      blockIsNotEntry predecessors (metadata.predecessors_sound blockIndex)
      candidateIndex waiting hcompute
  subst candidateIndex
  exact ⟨invariants.1, invariants.2,
    initialized_refine_target forest.not_bottom blockIndex candidate⟩

/-- Under the sweep invariant, every non-entry block computes a candidate. -/
theorem RegionMetadataForRegion.compute_exists [HasOpInfo OpInfo] [NeZero blockCount]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (blockIndex : Fin blockCount)
    (invariant : SweepInvariantForRegion value reversePostOrder region irCtx blockIndex.val)
    (blockIsNotEntry : blockIndex.val ≠ 0) :
    ∃ candidateIndex waiting,
      DominanceAnalysis.computeImmediateDominator
        blockIndex.val predecessors value = (some candidateIndex, waiting) := by
  let ordered := metadata.orderedForRegion
  obtain ⟨earlierPredecessor, earlier, earlierMem⟩ :=
    metadata.earlier_predecessor blockIndex blockIsNotEntry
  have earlierInitialized := invariant.initialized_before earlierPredecessor earlier
  have bounded := CandidateStateForBlock.fold_predecessors_bounded
    invariant.forest metadata.injective_rpo ordered blockIndex earlierPredecessor
      predecessors[blockIndex.val]! (metadata.predecessors_sound blockIndex)
      earlierMem earlierInitialized
  generalize hstate : predecessors[blockIndex.val]!.foldl
    (DominanceAnalysis.predecessorStep value) (none, false) = state at bounded
  obtain ⟨candidate, hcandidate, _, _⟩ := bounded
  refine ⟨candidate.val, state.2, ?_⟩
  unfold DominanceAnalysis.computeImmediateDominator
  simp only [blockIsNotEntry, ↓reduceIte, hstate]
  apply Prod.ext
  · exact hcandidate
  · rfl

/-- One executable non-entry update advances the initialized RPO prefix by one block. -/
theorem SweepInvariantForRegion.advance [HasOpInfo OpInfo] [NeZero blockCount]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (blockIndex : Fin blockCount)
    (invariant : SweepInvariantForRegion value reversePostOrder region irCtx blockIndex.val)
    (blockIsNotEntry : blockIndex.val ≠ 0)
    (candidateIndex : Nat)
    (waiting : Bool)
    (hcompute : DominanceAnalysis.computeImmediateDominator
      blockIndex.val predecessors value = (some candidateIndex, waiting)) :
    SweepInvariantForRegion
      (value.refine! blockIndex.val candidateIndex)
      reversePostOrder region irCtx (blockIndex.val + 1) := by
  let ordered := metadata.orderedForRegion
  obtain ⟨candidate, hcandidate, _⟩ :=
    computeImmediateDominator_partial invariant.forest metadata.injective_rpo ordered
      blockIndex blockIsNotEntry predecessors (metadata.predecessors_sound blockIndex)
      candidateIndex waiting hcompute
  have update := metadata.compute_refine_preserves invariant.forest invariant.sound
    blockIndex blockIsNotEntry invariant.initialized_before candidateIndex waiting hcompute
  subst candidateIndex
  refine ⟨update.1, update.2.1, ?_⟩
  intro queriedIndex hbefore
  by_cases hsame : queriedIndex = blockIndex
  · subst queriedIndex
    exact update.2.2
  · have holdInitialized := invariant.initialized_before queriedIndex (by
      have hneVal : queriedIndex.val ≠ blockIndex.val := by
        intro heq
        exact hsame (Fin.eq_of_val_eq heq)
      omega)
    exact holdInitialized.refine invariant.forest.not_bottom blockIndex candidate

/-- A non-waiting first-sweep update advances the stronger prefix invariant. -/
theorem InitialSweepInvariantForRegion.advance [HasOpInfo OpInfo] [NeZero blockCount]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (blockIndex : Fin blockCount)
    (invariant : InitialSweepInvariantForRegion value reversePostOrder predecessors
      region irCtx blockIndex.val)
    (blockIsNotEntry : blockIndex.val ≠ 0)
    (candidateIndex : Nat)
    (hcompute : DominanceAnalysis.computeImmediateDominator
      blockIndex.val predecessors value = (some candidateIndex, false)) :
    InitialSweepInvariantForRegion
      (value.refine! blockIndex.val candidateIndex)
      reversePostOrder predecessors region irCtx (blockIndex.val + 1) := by
  obtain ⟨candidate, candidateEq, _⟩ :=
    computeImmediateDominator_partial invariant.sweep.forest metadata.injective_rpo
      metadata.orderedForRegion blockIndex blockIsNotEntry predecessors
      (metadata.predecessors_sound blockIndex) candidateIndex false hcompute
  subst candidateIndex
  let refinedValue := value.refine! blockIndex.val candidate.val
  have advancedSweep := invariant.sweep.advance metadata blockIndex blockIsNotEntry
    candidate.val false hcompute
  have oldSentinel := invariant.uninitialized_from blockIndex (Nat.le_refl _)
  refine ⟨advancedSweep, ?_, ?_⟩
  · intro queriedIndex afterCurrent
    have queriedNe : queriedIndex ≠ blockIndex := by
      intro same
      subst queriedIndex
      omega
    rw [get!_refine_of_ne value invariant.sweep.forest.not_bottom blockIndex queriedIndex
      candidate queriedNe]
    exact invariant.uninitialized_from queriedIndex (by omega)
  · intro future futureNotBottom futureAgrees queriedIndex queriedBefore queriedNotEntry
    by_cases beforeCurrent : queriedIndex.val < blockIndex.val
    · apply invariant.prefix_fixed future futureNotBottom _ queriedIndex beforeCurrent
        queriedNotEntry
      intro earlierIndex earlierBefore
      have earlierNe : earlierIndex ≠ blockIndex := by
        intro same
        subst earlierIndex
        omega
      rw [← get!_refine_of_ne value invariant.sweep.forest.not_bottom blockIndex
        earlierIndex candidate earlierNe]
      exact futureAgrees earlierIndex (by omega)
    · have queriedEq : queriedIndex = blockIndex := by
        apply Fin.eq_of_val_eq
        omega
      subst queriedIndex
      have notWaiting := congrArg Prod.snd hcompute
      have predecessorsBefore := metadata.predecessors_before_of_not_waiting
        blockIndex blockIsNotEntry invariant.uninitialized_from notWaiting
      have oldFutureAgrees : AgreesBefore value future blockIndex.val := by
        intro earlierIndex earlierBefore
        have earlierNe : earlierIndex ≠ blockIndex := by
          intro same
          subst earlierIndex
          omega
        rw [← get!_refine_of_ne value invariant.sweep.forest.not_bottom blockIndex
          earlierIndex candidate earlierNe]
        exact futureAgrees earlierIndex (by omega)
      have computeEq := invariant.sweep.forest.compute_eq_of_agreesBefore blockIndex
        blockIsNotEntry invariant.sweep.initialized_before predecessors predecessorsBefore
        oldFutureAgrees
      have futureComputed : DominanceAnalysis.computeImmediateDominator
          blockIndex.val predecessors future = (some candidate.val, false) := by
        rw [← computeEq]
        exact hcompute
      have refinedGet : refinedValue.get? blockIndex.val = some candidate.val := by
        dsimp only [refinedValue]
        rw [get?_refine_eq_some_min value invariant.sweep.forest.not_bottom
          blockIndex candidate, oldSentinel]
        simp only [Nat.min_eq_right (Nat.le_of_lt candidate.isLt)]
      have encodedAgreement : refinedValue.get! blockIndex.val =
          future.get! blockIndex.val := futureAgrees blockIndex (by omega)
      have optionalAgreement := get?_eq_of_get!_eq refinedValue future
        advancedSweep.forest.not_bottom futureNotBottom blockIndex encodedAgreement
      calc
        (DominanceAnalysis.computeImmediateDominator
            blockIndex.val predecessors future).1 = some candidate.val :=
          congrArg Prod.fst futureComputed
        _ = refinedValue.get? blockIndex.val := refinedGet.symm
        _ = future.get? blockIndex.val := optionalAgreement

/-- A complete mathematical CHK sweep can advance any valid prefix to the end. -/
theorem RegionMetadataForRegion.completeSweepFrom [HasOpInfo OpInfo]
    [NeZero blockCount]
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (nextIndex : Nat)
    (nextPositive : 0 < nextIndex)
    (nextInBounds : nextIndex ≤ blockCount)
    (value : DominanceValue blockCount)
    (invariant : SweepInvariantForRegion value reversePostOrder region irCtx nextIndex) :
    ∃ sweptValue,
      SweepInvariantForRegion sweptValue reversePostOrder region irCtx blockCount := by
  by_cases finished : nextIndex = blockCount
  · subst nextIndex
    exact ⟨value, invariant⟩
  · have currentInBounds : nextIndex < blockCount := by omega
    let blockIndex : Fin blockCount := ⟨nextIndex, currentInBounds⟩
    have blockIsNotEntry : blockIndex.val ≠ 0 := by
      simpa only [blockIndex] using Nat.ne_of_gt nextPositive
    obtain ⟨candidateIndex, waiting, computed⟩ :=
      metadata.compute_exists blockIndex invariant blockIsNotEntry
    have advanced := invariant.advance metadata blockIndex blockIsNotEntry
      candidateIndex waiting computed
    exact metadata.completeSweepFrom (nextIndex + 1) (by omega) (by omega)
      (value.refine! blockIndex.val candidateIndex) advanced
termination_by blockCount - nextIndex
decreasing_by omega

/-- Starting from the CHK initial value, one complete RPO sweep initializes every block. -/
theorem RegionMetadataForRegion.initialCompleteSweep [HasOpInfo OpInfo]
    [NeZero blockCount]
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx) :
    ∃ sweptValue,
      SweepInvariantForRegion sweptValue reversePostOrder region irCtx blockCount := by
  have blockCountPositive : 0 < blockCount := Nat.pos_of_neZero blockCount
  exact metadata.completeSweepFrom 1 (by omega) (by omega)
    (initial blockCount) metadata.initial_sweepInvariant

/-- The first complete CHK sweep produces a sound, fully initialized working forest. -/
theorem RegionMetadataForRegion.firstSweepInvariants [HasOpInfo OpInfo]
    [NeZero blockCount]
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx) :
    ∃ sweptValue,
      WorkingForestForRegion sweptValue reversePostOrder region irCtx ∧
      SoundForRegion sweptValue reversePostOrder region irCtx ∧
      ∀ blockIndex : Fin blockCount, Initialized sweptValue blockIndex := by
  obtain ⟨sweptValue, invariant⟩ := metadata.initialCompleteSweep
  exact ⟨sweptValue, invariant.forest, invariant.sound,
    fun blockIndex => invariant.initialized_before blockIndex blockIndex.isLt⟩

open Std.Do in
set_option mvcgen.warning false in
set_option linter.deprecated.syntax false in
/-- The executable sweep advances a valid prefix through every non-entry RPO block. -/
theorem RegionMetadataForRegion.sweep_preserves [HasOpInfo OpInfo]
    [NeZero blockCount]
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (initialValue : DominanceValue blockCount)
    (initialInvariant : SweepInvariantForRegion initialValue reversePostOrder
      region irCtx 1) :
    SweepInvariantForRegion
      (DominanceAnalysis.sweep predecessors initialValue).latticeElement
      reversePostOrder region irCtx blockCount := by
  generalize resultEq : DominanceAnalysis.sweep predecessors initialValue = result
  apply Id.of_wp_run_eq resultEq
  simp only [WP.bind, SPred.entails_nil, SPred.down_pure, forall_const]
  mvcgen invariants
  | inv1 =>
      ⟨fun pair => ⌜SweepInvariantForRegion pair.2.1
        reversePostOrder region irCtx (1 + pair.1.pos)⌝,
        ExceptConds.false⟩
  all_goals mleave
  · next processed current remaining split state candidate candidateEq changed invariant =>
    have currentEq : current = 1 + processed.length := by
      have currentOption := congrArg (fun blocks => blocks[processed.length]?) split
      have processedInBounds : processed.length < [1:blockCount].toList.length := by
        rw [split]
        simp
      rw [List.getElem?_eq_getElem processedInBounds] at currentOption
      have getCurrent : [1:blockCount].toList[processed.length] = current := by
        simpa using currentOption
      simp only [Std.Legacy.Range.toList, List.getElem_range'] at getCurrent
      omega
    have currentInBounds : current < blockCount := by
      have currentMem : current ∈ [1:blockCount].toList := by
        rw [split]
        simp
      simp [Std.Legacy.Range.toList] at currentMem
      have positive : 0 < blockCount := Nat.pos_of_neZero blockCount
      omega
    let blockIndex : Fin blockCount := ⟨current, currentInBounds⟩
    have blockNotEntry : blockIndex.val ≠ 0 := by
      simp only [blockIndex]
      omega
    have invariantAtCurrent : SweepInvariantForRegion state.1 reversePostOrder
        region irCtx blockIndex.val := by
      simpa [List.Cursor.pos, blockIndex, currentEq] using invariant
    let waiting := (DominanceAnalysis.computeImmediateDominator
      current predecessors state.1).2
    have computed : DominanceAnalysis.computeImmediateDominator
        blockIndex.val predecessors state.1 = (some candidate, waiting) := by
      apply Prod.ext
      · exact candidateEq
      · rfl
    have advanced := invariantAtCurrent.advance metadata blockIndex blockNotEntry
      candidate waiting computed
    change SweepInvariantForRegion (state.1.refine! current candidate)
      reversePostOrder region irCtx (1 + (processed ++ [current]).length)
    have nextEq : 1 + (processed ++ [current]).length = blockIndex.val + 1 := by
      simp only [List.length_append, List.length_singleton, blockIndex]
      omega
    rw [nextEq]
    exact advanced
  · next processed current remaining split state candidate candidateEq unchanged invariant =>
    have currentEq : current = 1 + processed.length := by
      have currentOption := congrArg (fun blocks => blocks[processed.length]?) split
      have processedInBounds : processed.length < [1:blockCount].toList.length := by
        rw [split]
        simp
      rw [List.getElem?_eq_getElem processedInBounds] at currentOption
      have getCurrent : [1:blockCount].toList[processed.length] = current := by
        simpa using currentOption
      simp only [Std.Legacy.Range.toList, List.getElem_range'] at getCurrent
      omega
    have currentInBounds : current < blockCount := by
      have currentMem : current ∈ [1:blockCount].toList := by
        rw [split]
        simp
      simp [Std.Legacy.Range.toList] at currentMem
      have positive : 0 < blockCount := Nat.pos_of_neZero blockCount
      omega
    let blockIndex : Fin blockCount := ⟨current, currentInBounds⟩
    have blockNotEntry : blockIndex.val ≠ 0 := by
      simp only [blockIndex]
      omega
    have invariantAtCurrent : SweepInvariantForRegion state.1 reversePostOrder
        region irCtx blockIndex.val := by
      simpa [List.Cursor.pos, blockIndex, currentEq] using invariant
    let waiting := (DominanceAnalysis.computeImmediateDominator
      current predecessors state.1).2
    have computed : DominanceAnalysis.computeImmediateDominator
        blockIndex.val predecessors state.1 = (some candidate, waiting) := by
      apply Prod.ext
      · exact candidateEq
      · rfl
    have advanced := invariantAtCurrent.advance metadata blockIndex blockNotEntry
      candidate waiting computed
    have refinementEq : state.1.refine! current candidate = state.1 := by
      apply refine_eq_self_of_get_eq_min
      · exact invariantAtCurrent.forest.not_bottom
      · exact currentInBounds
      · obtain ⟨candidateFin, candidateFinEq, _⟩ :=
          computeImmediateDominator_partial invariantAtCurrent.forest
            metadata.injective_rpo metadata.orderedForRegion blockIndex
            blockNotEntry predecessors (metadata.predecessors_sound blockIndex)
            candidate waiting computed
        simp [candidateFinEq]
      · exact Decidable.not_not.mp unchanged
    rw [refinementEq] at advanced
    change SweepInvariantForRegion state.1 reversePostOrder region irCtx
      (1 + (processed ++ [current]).length)
    have nextEq : 1 + (processed ++ [current]).length = blockIndex.val + 1 := by
      simp only [List.length_append, List.length_singleton, blockIndex]
      omega
    rw [nextEq]
    exact advanced
  · next processed current remaining split state candidate noCandidate candidateEq invariant =>
    have currentEq : current = 1 + processed.length := by
      have currentOption := congrArg (fun blocks => blocks[processed.length]?) split
      have processedInBounds : processed.length < [1:blockCount].toList.length := by
        rw [split]
        simp
      rw [List.getElem?_eq_getElem processedInBounds] at currentOption
      have getCurrent : [1:blockCount].toList[processed.length] = current := by
        simpa using currentOption
      simp only [Std.Legacy.Range.toList, List.getElem_range'] at getCurrent
      omega
    have currentInBounds : current < blockCount := by
      have currentMem : current ∈ [1:blockCount].toList := by
        rw [split]
        simp
      simp [Std.Legacy.Range.toList] at currentMem
      have positive : 0 < blockCount := Nat.pos_of_neZero blockCount
      omega
    let blockIndex : Fin blockCount := ⟨current, currentInBounds⟩
    have blockNotEntry : blockIndex.val ≠ 0 := by
      simp only [blockIndex]
      omega
    have invariantAtCurrent : SweepInvariantForRegion state.1 reversePostOrder
        region irCtx blockIndex.val := by
      simpa [List.Cursor.pos, blockIndex, currentEq] using invariant
    obtain ⟨computedCandidate, waiting, computed⟩ :=
      metadata.compute_exists blockIndex invariantAtCurrent blockNotEntry
    have firstComponent :
        (DominanceAnalysis.computeImmediateDominator current predecessors state.1).1 =
          some computedCandidate := by
      simpa [blockIndex] using congrArg Prod.fst computed
    rw [candidateEq] at firstComponent
    exact False.elim (noCandidate computedCandidate firstComponent)
  · next state invariant =>
    have rangeLength : 1 + [1:blockCount].toList.length = blockCount := by
      simp only [Std.Legacy.Range.toList, List.length_range']
      have positive : 0 < blockCount := Nat.pos_of_neZero blockCount
      simp
      omega
    change SweepInvariantForRegion state.1 reversePostOrder region irCtx
      (1 + [1:blockCount].toList.length) at invariant
    rw [rangeLength] at invariant
    exact invariant

open Std.Do in
set_option mvcgen.warning false in
set_option linter.deprecated.syntax false in
/-- A non-requeued first executable sweep satisfies the strong first-sweep invariant. -/
theorem RegionMetadataForRegion.initial_sweepInvariant_of_not_needed [HasOpInfo OpInfo]
    [NeZero blockCount]
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (notNeeded :
      (DominanceAnalysis.sweep predecessors (initial blockCount)).needsSweep = false) :
    InitialSweepInvariantForRegion
      (DominanceAnalysis.sweep predecessors (initial blockCount)).latticeElement
      reversePostOrder predecessors region irCtx blockCount := by
  generalize resultEq : DominanceAnalysis.sweep predecessors (initial blockCount) = result
    at notNeeded ⊢
  revert notNeeded
  apply Id.of_wp_run_eq resultEq
  simp only [WP.bind, SPred.entails_nil, SPred.down_pure, forall_const]
  mvcgen invariants
  | inv1 =>
      ⟨fun pair => ⌜pair.2.2.2 = false →
          InitialSweepInvariantForRegion pair.2.1 reversePostOrder predecessors
            region irCtx (1 + pair.1.pos)⌝,
        ExceptConds.false⟩
  all_goals mleave
  · next processed current remaining split state candidate candidateEq changed invariant =>
    intro finalNotNeeded
    obtain ⟨oldAndWaitingFalse, _⟩ := Bool.or_eq_false_iff.mp finalNotNeeded
    obtain ⟨oldNotNeeded, waitingFalse⟩ := Bool.or_eq_false_iff.mp oldAndWaitingFalse
    have invariantAtPrefix := invariant oldNotNeeded
    have currentEq : current = 1 + processed.length := by
      have currentOption := congrArg (fun blocks => blocks[processed.length]?) split
      have processedInBounds : processed.length < [1:blockCount].toList.length := by
        rw [split]
        simp
      rw [List.getElem?_eq_getElem processedInBounds] at currentOption
      have getCurrent : [1:blockCount].toList[processed.length] = current := by
        simpa using currentOption
      simp only [Std.Legacy.Range.toList, List.getElem_range'] at getCurrent
      omega
    have currentInBounds : current < blockCount := by
      have currentMem : current ∈ [1:blockCount].toList := by
        rw [split]
        simp
      simp [Std.Legacy.Range.toList] at currentMem
      omega
    let blockIndex : Fin blockCount := ⟨current, currentInBounds⟩
    have blockNotEntry : blockIndex.val ≠ 0 := by
      simp only [blockIndex]
      omega
    let waiting := (DominanceAnalysis.computeImmediateDominator
      current predecessors state.1).2
    have waitingEq : waiting = false := by
      exact waitingFalse
    have computed : DominanceAnalysis.computeImmediateDominator
        blockIndex.val predecessors state.1 = (some candidate, false) := by
      apply Prod.ext
      · exact candidateEq
      · exact waitingEq
    have prefixEq : 1 + processed.length = blockIndex.val := by
      simp only [blockIndex]
      omega
    rw [prefixEq] at invariantAtPrefix
    have advanced := invariantAtPrefix.advance metadata blockIndex blockNotEntry
      candidate computed
    change InitialSweepInvariantForRegion (state.1.refine! current candidate)
      reversePostOrder predecessors region irCtx (1 + (processed ++ [current]).length)
    have nextEq : 1 + (processed ++ [current]).length = blockIndex.val + 1 := by
      simp only [List.length_append, List.length_singleton, blockIndex]
      omega
    rw [nextEq]
    exact advanced
  · next processed current remaining split state candidate candidateEq unchanged invariant =>
    intro finalNotNeeded
    obtain ⟨oldAndWaitingFalse, _⟩ := Bool.or_eq_false_iff.mp finalNotNeeded
    obtain ⟨oldNotNeeded, waitingFalse⟩ := Bool.or_eq_false_iff.mp oldAndWaitingFalse
    have invariantAtPrefix := invariant oldNotNeeded
    have currentEq : current = 1 + processed.length := by
      have currentOption := congrArg (fun blocks => blocks[processed.length]?) split
      have processedInBounds : processed.length < [1:blockCount].toList.length := by
        rw [split]
        simp
      rw [List.getElem?_eq_getElem processedInBounds] at currentOption
      have getCurrent : [1:blockCount].toList[processed.length] = current := by
        simpa using currentOption
      simp only [Std.Legacy.Range.toList, List.getElem_range'] at getCurrent
      omega
    have currentInBounds : current < blockCount := by
      have currentMem : current ∈ [1:blockCount].toList := by
        rw [split]
        simp
      simp [Std.Legacy.Range.toList] at currentMem
      omega
    let blockIndex : Fin blockCount := ⟨current, currentInBounds⟩
    have blockNotEntry : blockIndex.val ≠ 0 := by
      simp only [blockIndex]
      omega
    let waiting := (DominanceAnalysis.computeImmediateDominator
      current predecessors state.1).2
    have waitingEq : waiting = false := waitingFalse
    have computed : DominanceAnalysis.computeImmediateDominator
        blockIndex.val predecessors state.1 = (some candidate, false) := by
      apply Prod.ext
      · exact candidateEq
      · exact waitingEq
    have prefixEq : 1 + processed.length = blockIndex.val := by
      simp only [blockIndex]
      omega
    rw [prefixEq] at invariantAtPrefix
    obtain ⟨candidateFin, candidateFinEq, _⟩ :=
      computeImmediateDominator_partial invariantAtPrefix.sweep.forest
        metadata.injective_rpo metadata.orderedForRegion blockIndex blockNotEntry
        predecessors (metadata.predecessors_sound blockIndex) candidate false computed
    have oldSentinel := invariantAtPrefix.uninitialized_from blockIndex (Nat.le_refl _)
    have oldEqMin := Decidable.not_not.mp unchanged
    rw [oldSentinel, candidateFinEq, Nat.min_eq_right (Nat.le_of_lt candidateFin.isLt)]
      at oldEqMin
    omega
  · next processed current remaining split state candidate noCandidate candidateEq invariant =>
    intro finalNotNeeded
    obtain ⟨oldNotNeeded, _⟩ := Bool.or_eq_false_iff.mp finalNotNeeded
    have invariantAtPrefix := invariant oldNotNeeded
    have currentEq : current = 1 + processed.length := by
      have currentOption := congrArg (fun blocks => blocks[processed.length]?) split
      have processedInBounds : processed.length < [1:blockCount].toList.length := by
        rw [split]
        simp
      rw [List.getElem?_eq_getElem processedInBounds] at currentOption
      have getCurrent : [1:blockCount].toList[processed.length] = current := by
        simpa using currentOption
      simp only [Std.Legacy.Range.toList, List.getElem_range'] at getCurrent
      omega
    have currentInBounds : current < blockCount := by
      have currentMem : current ∈ [1:blockCount].toList := by
        rw [split]
        simp
      simp [Std.Legacy.Range.toList] at currentMem
      omega
    let blockIndex : Fin blockCount := ⟨current, currentInBounds⟩
    have blockNotEntry : blockIndex.val ≠ 0 := by
      simp only [blockIndex]
      omega
    have prefixEq : 1 + processed.length = blockIndex.val := by
      simp only [blockIndex]
      omega
    rw [prefixEq] at invariantAtPrefix
    obtain ⟨computedCandidate, waiting, computed⟩ :=
      metadata.compute_exists blockIndex invariantAtPrefix.sweep blockNotEntry
    have candidateIsSome : candidate = some computedCandidate := by
      exact candidateEq.symm.trans (congrArg Prod.fst computed)
    exact False.elim (noCandidate computedCandidate candidateIsSome)
  · simpa [List.Cursor.pos] using metadata.initial_firstSweepInvariant
  · next state invariant =>
    intro finalNotNeeded
    have rangeLength : 1 + [1:blockCount].toList.length = blockCount := by
      simp only [Std.Legacy.Range.toList, List.length_range']
      have positive : 0 < blockCount := Nat.pos_of_neZero blockCount
      simp
      omega
    have finalInvariant := invariant finalNotNeeded
    rw [rangeLength] at finalInvariant
    exact finalInvariant

/-- The executable first sweep produces a sound, fully initialized working forest. -/
theorem RegionMetadataForRegion.initialSweepInvariants [HasOpInfo OpInfo]
    [NeZero blockCount]
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx) :
    let sweptValue :=
      (DominanceAnalysis.sweep predecessors (initial blockCount)).latticeElement
    WorkingForestForRegion sweptValue reversePostOrder region irCtx ∧
      SoundForRegion sweptValue reversePostOrder region irCtx ∧
      ∀ blockIndex : Fin blockCount, Initialized sweptValue blockIndex := by
  let sweptValue :=
    (DominanceAnalysis.sweep predecessors (initial blockCount)).latticeElement
  have invariant := metadata.sweep_preserves
    (initial blockCount) metadata.initial_sweepInvariant
  exact ⟨invariant.forest, invariant.sound,
    fun blockIndex => invariant.initialized_before blockIndex blockIndex.isLt⟩

/-- The persistent semantic invariants after the first complete CHK sweep. -/
structure SolverInvariantForRegion [HasOpInfo OpInfo]
    (value : DominanceValue blockCount)
    (reversePostOrder : Vector BlockPtr blockCount)
    (region : RegionPtr)
    (irCtx : WfIRContext OpInfo) : Prop where
  forest : WorkingForestForRegion value reversePostOrder region irCtx
  sound : SoundForRegion value reversePostOrder region irCtx
  initialized : ∀ blockIndex : Fin blockCount, Initialized value blockIndex

/-- Every non-entry block's stored parent equals the current CHK predecessor fold. -/
def CHKFixedPoint
    (predecessors : Array (Array Nat))
    (value : DominanceValue blockCount) : Prop :=
  ∀ blockIndex : Fin blockCount,
    blockIndex.val ≠ 0 →
    (DominanceAnalysis.computeImmediateDominator
      blockIndex.val predecessors value).1 = value.get? blockIndex.val

/-- A first sweep that does not requeue already satisfies every CHK equation. -/
theorem RegionMetadataForRegion.initial_sweep_not_needed_fixedPoint [HasOpInfo OpInfo]
    [NeZero blockCount]
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (notNeeded :
      (DominanceAnalysis.sweep predecessors (initial blockCount)).needsSweep = false) :
    CHKFixedPoint predecessors
      (DominanceAnalysis.sweep predecessors (initial blockCount)).latticeElement := by
  have invariant := metadata.initial_sweepInvariant_of_not_needed notNeeded
  intro blockIndex blockNotEntry
  apply invariant.prefix_fixed
  · exact invariant.sweep.forest.not_bottom
  · intro queriedIndex _
    rfl
  · exact blockIndex.isLt
  · exact blockNotEntry

/-- A fully initialized solver state supplies the prefix invariant for another sweep. -/
theorem SolverInvariantForRegion.sweepInvariant [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (invariant : SolverInvariantForRegion value reversePostOrder region irCtx) :
    SweepInvariantForRegion value reversePostOrder region irCtx 1 := by
  exact ⟨invariant.forest, invariant.sound,
    fun blockIndex _ => invariant.initialized blockIndex⟩

/-- Every later executable sweep preserves soundness and full initialization. -/
theorem RegionMetadataForRegion.sweep_preserves_solverInvariant [HasOpInfo OpInfo]
    [NeZero blockCount]
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (value : DominanceValue blockCount)
    (invariant : SolverInvariantForRegion value reversePostOrder region irCtx) :
    SolverInvariantForRegion
      (DominanceAnalysis.sweep predecessors value).latticeElement
      reversePostOrder region irCtx := by
  have swept := metadata.sweep_preserves value invariant.sweepInvariant
  exact ⟨swept.forest, swept.sound,
    fun blockIndex => swept.initialized_before blockIndex blockIndex.isLt⟩

/-- The executable initial sweep establishes the persistent solver invariant. -/
theorem RegionMetadataForRegion.initialSolverInvariant [HasOpInfo OpInfo]
    [NeZero blockCount]
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx) :
    SolverInvariantForRegion
      (DominanceAnalysis.sweep predecessors (initial blockCount)).latticeElement
      reversePostOrder region irCtx := by
  obtain ⟨forest, sound, initialized⟩ := metadata.initialSweepInvariants
  exact ⟨forest, sound, initialized⟩

open Std.Do in
set_option mvcgen.warning false in
set_option linter.deprecated.syntax false in
set_option maxRecDepth 4096 in
/-- A completed sweep that does not requeue the region satisfies the exact CHK equations. -/
theorem RegionMetadataForRegion.sweep_not_needed_fixedPoint [HasOpInfo OpInfo]
    [NeZero blockCount]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (invariant : SolverInvariantForRegion value reversePostOrder region irCtx)
    (notNeeded : (DominanceAnalysis.sweep predecessors value).needsSweep = false) :
    CHKFixedPoint predecessors value := by
  generalize resultEq : DominanceAnalysis.sweep predecessors value = result at notNeeded
  revert notNeeded
  apply Id.of_wp_run_eq resultEq
  simp only [WP.bind, SPred.entails_nil, SPred.down_pure, forall_const]
  mvcgen invariants
  | inv1 =>
      ⟨fun pair => ⌜pair.2.2.2 = false →
          pair.2.1 = value ∧
            ∀ blockIndex : Fin blockCount,
              blockIndex.val ∈ pair.1.prefix →
              (DominanceAnalysis.computeImmediateDominator
                blockIndex.val predecessors value).1 = value.get? blockIndex.val⌝,
        ExceptConds.false⟩
  all_goals mleave
  · next pref current suffix split state candidate candidateEq refined invariantAtPrefix =>
    intro finalNotNeeded
    obtain ⟨oldAndWaitingFalse, mismatchFalse⟩ :=
      Bool.or_eq_false_iff.mp finalNotNeeded
    obtain ⟨oldNotNeeded, _⟩ := Bool.or_eq_false_iff.mp oldAndWaitingFalse
    obtain ⟨stateEq, _⟩ := invariantAtPrefix oldNotNeeded
    have currentMem : current ∈ [1:blockCount].toList := by
      rw [split]
      simp
    have currentInBounds : current < blockCount := by
      simp [Std.Legacy.Range.toList] at currentMem
      omega
    let currentIndex : Fin blockCount := ⟨current, currentInBounds⟩
    obtain ⟨parentIndex, parentEq⟩ := invariant.initialized currentIndex
    have encodedParent :=
      get!_eq_of_get?_eq_some value currentIndex parentIndex parentEq
    have oldNotTop : value.get! current ≠ blockCount := by
      rw [encodedParent]
      exact Nat.ne_of_lt parentIndex.isLt
    have oldNeCandidate : value.get! current ≠ candidate := by
      intro oldEq
      rw [stateEq, oldEq, Nat.min_self] at refined
      contradiction
    rw [stateEq] at mismatchFalse
    simp [oldNotTop, oldNeCandidate] at mismatchFalse
  · next pref current suffix split state candidate candidateEq unchanged invariantAtPrefix =>
    intro finalNotNeeded
    obtain ⟨oldAndWaitingFalse, mismatchFalse⟩ :=
      Bool.or_eq_false_iff.mp finalNotNeeded
    obtain ⟨oldNotNeeded, _⟩ := Bool.or_eq_false_iff.mp oldAndWaitingFalse
    obtain ⟨stateEq, previousFixed⟩ := invariantAtPrefix oldNotNeeded
    have currentMem : current ∈ [1:blockCount].toList := by
      rw [split]
      simp
    have currentInBounds : current < blockCount := by
      simp [Std.Legacy.Range.toList] at currentMem
      omega
    let currentIndex : Fin blockCount := ⟨current, currentInBounds⟩
    obtain ⟨parentIndex, parentEq⟩ := invariant.initialized currentIndex
    have encodedParent :=
      get!_eq_of_get?_eq_some value currentIndex parentIndex parentEq
    have oldNotTop : value.get! current ≠ blockCount := by
      rw [encodedParent]
      exact Nat.ne_of_lt parentIndex.isLt
    have oldEqCandidate : value.get! current = candidate := by
      by_cases oldEqCandidate : value.get! current = candidate
      · exact oldEqCandidate
      · rw [stateEq] at mismatchFalse
        simp [oldNotTop, oldEqCandidate] at mismatchFalse
    have currentFixed :
        (DominanceAnalysis.computeImmediateDominator current predecessors value).1 =
          value.get? current := by
      rw [stateEq] at candidateEq
      rw [candidateEq, parentEq]
      exact congrArg some (oldEqCandidate.symm.trans encodedParent)
    refine ⟨stateEq, ?_⟩
    intro blockIndex blockMem
    simp only [List.mem_append, List.mem_singleton] at blockMem
    rcases blockMem with oldBlock | currentBlock
    · exact previousFixed blockIndex oldBlock
    · simpa only [currentBlock] using currentFixed
  · next pref current suffix split state candidate noCandidate candidateEq invariantAtPrefix =>
    intro finalNotNeeded
    obtain ⟨oldNotNeeded, _⟩ := Bool.or_eq_false_iff.mp finalNotNeeded
    obtain ⟨stateEq, _⟩ := invariantAtPrefix oldNotNeeded
    have currentMem : current ∈ [1:blockCount].toList := by
      rw [split]
      simp
    have currentInBounds : current < blockCount := by
      simp [Std.Legacy.Range.toList] at currentMem
      omega
    have currentEq : current = 1 + pref.length := by
      have currentOption := congrArg (fun blocks => blocks[pref.length]?) split
      have prefInBounds : pref.length < [1:blockCount].toList.length := by
        rw [split]
        simp
      rw [List.getElem?_eq_getElem prefInBounds] at currentOption
      have getCurrent : [1:blockCount].toList[pref.length] = current := by
        simpa using currentOption
      simp only [Std.Legacy.Range.toList, List.getElem_range'] at getCurrent
      omega
    let currentIndex : Fin blockCount := ⟨current, currentInBounds⟩
    have currentNotEntry : currentIndex.val ≠ 0 := by
      simp only [currentIndex]
      omega
    let currentInvariant : SweepInvariantForRegion value reversePostOrder
        region irCtx currentIndex.val :=
      ⟨invariant.forest, invariant.sound,
        fun blockIndex _ => invariant.initialized blockIndex⟩
    obtain ⟨computedCandidate, waiting, computed⟩ :=
      metadata.compute_exists currentIndex currentInvariant currentNotEntry
    have candidateIsSome : candidate = some computedCandidate := by
      rw [stateEq] at candidateEq
      exact candidateEq.symm.trans (congrArg Prod.fst computed)
    exact False.elim (noCandidate computedCandidate candidateIsSome)
  · constructor
    · trivial
    · intro blockIndex blockMem
      simp at blockMem
  · next finalState finalInvariant =>
    intro finalNotNeeded
    obtain ⟨_, fixed⟩ := finalInvariant finalNotNeeded
    intro blockIndex blockNotEntry
    apply fixed blockIndex
    simp [Std.Legacy.Range.toList]
    omega

/-- Working ancestry in a fully initialized descending forest moves toward earlier indices. -/
theorem SolverInvariantForRegion.ancestor_le [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (invariant : SolverInvariantForRegion value reversePostOrder region irCtx)
    (ancestor descendant : Fin blockCount)
    (ancestry : WorkingAncestor value ancestor.val descendant.val) :
    ancestor ≤ descendant := by
  have go : ∀ {ancestorIndex descendantIndex : Nat},
      WorkingAncestor value ancestorIndex descendantIndex →
      ancestorIndex < blockCount → descendantIndex < blockCount →
      ancestorIndex ≤ descendantIndex := by
    intro ancestorIndex descendantIndex ancestry
    induction ancestry with
    | refl =>
        intro _ _
        exact Nat.le_refl _
    | parent tail ih =>
        rename_i child
        intro ancestorInBounds childInBounds
        let childIndex : Fin blockCount := ⟨child, childInBounds⟩
        obtain ⟨parentIndex, parentEq⟩ := invariant.initialized childIndex
        have encodedParent :=
          get!_eq_of_get?_eq_some value childIndex parentIndex parentEq
        have ancestorLeParent : ancestorIndex ≤ parentIndex.val := by
          rw [← encodedParent]
          apply ih
          · exact ancestorInBounds
          · rw [encodedParent]
            exact parentIndex.isLt
        rcases invariant.forest.parent_decreases childIndex parentIndex parentEq with
          entry | decreases
        · have childIsZero : child = 0 := by
            simpa only [childIndex] using entry.1
          have parentIsZero : parentIndex.val = 0 := entry.2
          omega
        · exact Nat.le_trans ancestorLeParent (Nat.le_of_lt decreases)
  exact go ancestry ancestor.isLt descendant.isLt

/-- At a CHK fixed point, a block's stored parent is a working ancestor of every predecessor. -/
theorem SolverInvariantForRegion.parent_ancestor_of_predecessor [HasOpInfo OpInfo]
    [NeZero blockCount]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (complete : PredecessorTableCompleteForRegion reversePostOrder predecessors irCtx)
    (invariant : SolverInvariantForRegion value reversePostOrder region irCtx)
    (fixed : CHKFixedPoint predecessors value)
    (blockIndex parentIndex predecessorIndex : Fin blockCount)
    (blockIsNotEntry : blockIndex.val ≠ 0)
    (parentEq : value.get? blockIndex.val = some parentIndex.val)
    (edge : reversePostOrder.get blockIndex ∈
      (reversePostOrder.get predecessorIndex).getSuccessors! irCtx.raw) :
    WorkingAncestor value parentIndex.val predecessorIndex.val := by
  let ordered := metadata.orderedForRegion
  have predecessorsSound := metadata.predecessors_sound blockIndex
  have allInitialized : ∀ predecessor ∈ predecessors[blockIndex.val]!,
      ∃ predecessorFin : Fin blockCount,
        predecessorFin.val = predecessor ∧ Initialized value predecessorFin := by
    intro predecessor predecessorMem
    obtain ⟨predecessorFin, predecessorEq, _, _⟩ :=
      predecessorsSound predecessor predecessorMem
    exact ⟨predecessorFin, predecessorEq, invariant.initialized predecessorFin⟩
  have predecessorMem := complete blockIndex predecessorIndex edge
  have candidateAncestor := CandidateStateForBlock.fold_predecessors_ancestor
    invariant.forest metadata.injective_rpo ordered blockIndex
    predecessors[blockIndex.val]! predecessorsSound allInitialized predecessorIndex.val
    predecessorMem
  have fixedEq := fixed blockIndex blockIsNotEntry
  unfold DominanceAnalysis.computeImmediateDominator at fixedEq
  simp only [blockIsNotEntry, ↓reduceIte] at fixedEq
  rw [parentEq] at fixedEq
  obtain ⟨candidateIndex, candidateEq, ancestor⟩ := candidateAncestor
  rw [candidateEq] at fixedEq
  have candidateIsParent : candidateIndex = parentIndex.val := Option.some.inj fixedEq
  rwa [candidateIsParent] at ancestor

/-- Every working ancestor occurs on every entry path once the CHK equations are stable. -/
theorem SolverInvariantForRegion.workingAncestor_mem_of_entry_path [HasOpInfo OpInfo]
    [NeZero blockCount]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (complete : PredecessorTableCompleteForRegion reversePostOrder predecessors irCtx)
    (represented : ReachableBlocksRepresented reversePostOrder region irCtx)
    (invariant : SolverInvariantForRegion value reversePostOrder region irCtx)
    (fixed : CHKFixedPoint predecessors value)
    (ancestorIndex targetIndex : Fin blockCount)
    (ancestry : WorkingAncestor value ancestorIndex.val targetIndex.val)
    (blocks : List BlockPtr)
    (path : region.Path irCtx
      (reversePostOrder.get ⟨0, Nat.pos_of_neZero blockCount⟩)
      (reversePostOrder.get targetIndex) blocks) :
    reversePostOrder.get ancestorIndex ∈ blocks := by
  by_cases ancestorIsTarget : ancestorIndex = targetIndex
  · subst ancestorIndex
    exact path.target_mem
  have targetIsNotEntry : targetIndex.val ≠ 0 := by
    intro targetIsEntry
    have ancestorLeTarget := invariant.ancestor_le ancestorIndex targetIndex ancestry
    have ancestorIsEntry : ancestorIndex.val = 0 := by omega
    exact ancestorIsTarget (Fin.eq_of_val_eq (ancestorIsEntry.trans targetIsEntry.symm))
  rcases path.eq_single_or_exists_unsnoc with single | unsnoc
  · obtain ⟨entryIsTarget, blocksEq⟩ := single
    have targetIsEntry : targetIndex = ⟨0, Nat.pos_of_neZero blockCount⟩ := by
      apply metadata.injective_rpo
      exact entryIsTarget.symm
    exact False.elim (targetIsNotEntry (congrArg Fin.val targetIsEntry))
  · obtain ⟨predecessor, prefixBlocks, prefixPath, edge, blocksEq⟩ := unsnoc
    have predecessorReachable : predecessor.ReachableFromEntry region irCtx :=
      BlockPtr.ReachableFromEntry.of_path metadata.entry_is_first prefixPath
    obtain ⟨predecessorIndex, predecessorEq⟩ :=
      represented predecessor predecessorReachable
    obtain ⟨parentIndex, parentEq⟩ := invariant.initialized targetIndex
    have encodedParent :=
      get!_eq_of_get?_eq_some value targetIndex parentIndex parentEq
    rcases ancestry.eq_or_parent with sameIndex | tail
    · exact False.elim (ancestorIsTarget (Fin.eq_of_val_eq sameIndex))
    ·
        have tail' : WorkingAncestor value ancestorIndex.val parentIndex.val := by
          rwa [encodedParent] at tail
        have representedEdge : reversePostOrder.get targetIndex ∈
            (reversePostOrder.get predecessorIndex).getSuccessors! irCtx.raw := by
          rw [predecessorEq]
          exact edge
        have parentAncestry := invariant.parent_ancestor_of_predecessor metadata complete
          fixed targetIndex parentIndex predecessorIndex targetIsNotEntry parentEq representedEdge
        have ancestryToPredecessor := tail'.trans parentAncestry
        have representedPrefixPath : region.Path irCtx
            (reversePostOrder.get ⟨0, Nat.pos_of_neZero blockCount⟩)
            (reversePostOrder.get predecessorIndex) prefixBlocks := by
          rw [predecessorEq]
          exact prefixPath
        have ancestorMem := invariant.workingAncestor_mem_of_entry_path metadata complete
          represented fixed ancestorIndex predecessorIndex ancestryToPredecessor
          prefixBlocks representedPrefixPath
        rw [blocksEq]
        exact List.mem_append_left [reversePostOrder.get targetIndex] ancestorMem
termination_by blocks.length
decreasing_by
  simp only [blocksEq, List.length_append, List.length_singleton]
  omega

/-- A non-entry block's stored parent is a semantic proper dominator at a CHK fixed point. -/
theorem SolverInvariantForRegion.parent_properlyDominates [HasOpInfo OpInfo]
    [NeZero blockCount]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (complete : PredecessorTableCompleteForRegion reversePostOrder predecessors irCtx)
    (represented : ReachableBlocksRepresented reversePostOrder region irCtx)
    (invariant : SolverInvariantForRegion value reversePostOrder region irCtx)
    (fixed : CHKFixedPoint predecessors value)
    (blockIndex parentIndex semanticIDomIndex : Fin blockCount)
    (parentEq : value.get? blockIndex.val = some parentIndex.val)
    (semanticIDom :
      (reversePostOrder.get semanticIDomIndex).ImmediateDominatorInSSACFGRegion
        (reversePostOrder.get blockIndex) region irCtx) :
    (reversePostOrder.get parentIndex).ProperlyDominatesInSSACFGRegion
      (reversePostOrder.get blockIndex) region irCtx := by
  let ordered := metadata.orderedForRegion
  have semanticIDomEarlier :=
    immediateDominator_index_lt ordered blockIndex semanticIDomIndex semanticIDom
  have blockIsNotEntry : blockIndex.val ≠ 0 := by omega
  have parentDecreases : parentIndex < blockIndex := by
    rcases invariant.forest.parent_decreases blockIndex parentIndex parentEq with
      entry | decreases
    · exact False.elim (blockIsNotEntry entry.1)
    · exact decreases
  have encodedParent :=
    get!_eq_of_get?_eq_some value blockIndex parentIndex parentEq
  have parentAncestry : WorkingAncestor value parentIndex.val blockIndex.val := by
    apply WorkingAncestor.parent
    rw [encodedParent]
    exact WorkingAncestor.refl parentIndex.val
  have semanticProper := semanticIDom.1
  unfold BlockPtr.ProperlyDominatesInSSACFGRegion at semanticProper
  rcases semanticProper with
    ⟨_, _, regionHasSSADominance, _, _⟩
  refine ⟨metadata.blocks_parent parentIndex, metadata.blocks_parent blockIndex,
    regionHasSSADominance, ?_, ?_⟩
  · intro blocksEqual
    have indicesEqual := metadata.injective_rpo blocksEqual
    exact Fin.ne_of_lt parentDecreases indicesEqual
  · intro entry blocks entryIsFirst path
    have entryEqual :
        reversePostOrder.get ⟨0, Nat.pos_of_neZero blockCount⟩ = entry := by
      rw [metadata.entry_is_first] at entryIsFirst
      exact Option.some.inj entryIsFirst
    subst entry
    exact invariant.workingAncestor_mem_of_entry_path metadata complete represented fixed
      parentIndex blockIndex parentAncestry blocks path

/-- The stable CHK parent equals the path-semantics immediate dominator. -/
theorem SolverInvariantForRegion.fixedPoint_parent_eq_immediateDominator
    [HasOpInfo OpInfo] [NeZero blockCount]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (complete : PredecessorTableCompleteForRegion reversePostOrder predecessors irCtx)
    (represented : ReachableBlocksRepresented reversePostOrder region irCtx)
    (invariant : SolverInvariantForRegion value reversePostOrder region irCtx)
    (fixed : CHKFixedPoint predecessors value)
    (blockIndex parentIndex semanticIDomIndex : Fin blockCount)
    (parentEq : value.get? blockIndex.val = some parentIndex.val)
    (semanticIDom :
      (reversePostOrder.get semanticIDomIndex).ImmediateDominatorInSSACFGRegion
        (reversePostOrder.get blockIndex) region irCtx) :
    parentIndex = semanticIDomIndex := by
  let ordered := metadata.orderedForRegion
  have semanticIDomEarlier :=
    immediateDominator_index_lt ordered blockIndex semanticIDomIndex semanticIDom
  have parentProper := invariant.parent_properlyDominates metadata complete represented fixed
    blockIndex parentIndex semanticIDomIndex parentEq semanticIDom
  have parentDominatesSemanticIDom := semanticIDom.2 _ parentProper
  have semanticIDomDominatesParent := invariant.forest.preserves_strict_dominators
    blockIndex parentIndex semanticIDomIndex parentEq semanticIDomEarlier (Or.inr semanticIDom.1)
  apply Fin.eq_of_val_eq
  exact Nat.le_antisymm
    (ordered parentIndex semanticIDomIndex parentDominatesSemanticIDom)
    (ordered semanticIDomIndex parentIndex semanticIDomDominatesParent)

/-- A non-requeued initial sweep stores every path-semantics immediate dominator. -/
theorem RegionMetadataForRegion.initial_stableSweep_correct
    [HasOpInfo OpInfo] [NeZero blockCount]
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (complete : PredecessorTableCompleteForRegion reversePostOrder predecessors irCtx)
    (represented : ReachableBlocksRepresented reversePostOrder region irCtx)
    (notNeeded :
      (DominanceAnalysis.sweep predecessors (initial blockCount)).needsSweep = false)
    (blockIndex semanticIDomIndex : Fin blockCount)
    (semanticIDom :
      (reversePostOrder.get semanticIDomIndex).ImmediateDominatorInSSACFGRegion
        (reversePostOrder.get blockIndex) region irCtx) :
    (DominanceAnalysis.sweep predecessors (initial blockCount)).latticeElement.get?
        blockIndex.val = some semanticIDomIndex.val := by
  let value :=
    (DominanceAnalysis.sweep predecessors (initial blockCount)).latticeElement
  have invariant := metadata.initialSolverInvariant
  have fixed := metadata.initial_sweep_not_needed_fixedPoint notNeeded
  obtain ⟨parentIndex, parentEq⟩ := invariant.initialized blockIndex
  have parentIsSemantic := invariant.fixedPoint_parent_eq_immediateDominator
    metadata complete represented fixed blockIndex parentIndex semanticIDomIndex
    parentEq semanticIDom
  subst parentIndex
  exact parentEq

/-- A solver state that completes a sweep without requeueing stores the semantic iDom. -/
theorem RegionMetadataForRegion.stableSweep_parent_eq_immediateDominator
    [HasOpInfo OpInfo] [NeZero blockCount]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (complete : PredecessorTableCompleteForRegion reversePostOrder predecessors irCtx)
    (represented : ReachableBlocksRepresented reversePostOrder region irCtx)
    (invariant : SolverInvariantForRegion value reversePostOrder region irCtx)
    (notNeeded : (DominanceAnalysis.sweep predecessors value).needsSweep = false)
    (blockIndex parentIndex semanticIDomIndex : Fin blockCount)
    (parentEq : value.get? blockIndex.val = some parentIndex.val)
    (semanticIDom :
      (reversePostOrder.get semanticIDomIndex).ImmediateDominatorInSSACFGRegion
        (reversePostOrder.get blockIndex) region irCtx) :
    parentIndex = semanticIDomIndex := by
  have fixed := metadata.sweep_not_needed_fixedPoint invariant notNeeded
  exact invariant.fixedPoint_parent_eq_immediateDominator metadata complete represented fixed
    blockIndex parentIndex semanticIDomIndex parentEq semanticIDom

/-- At a stable sweep, every stored non-entry parent is the path-semantics immediate dominator. -/
theorem RegionMetadataForRegion.stableSweep_correct
    [HasOpInfo OpInfo] [NeZero blockCount]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {predecessors : Array (Array Nat)}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (metadata : RegionMetadataForRegion reversePostOrder predecessors region irCtx)
    (complete : PredecessorTableCompleteForRegion reversePostOrder predecessors irCtx)
    (represented : ReachableBlocksRepresented reversePostOrder region irCtx)
    (invariant : SolverInvariantForRegion value reversePostOrder region irCtx)
    (notNeeded : (DominanceAnalysis.sweep predecessors value).needsSweep = false)
    (blockIndex semanticIDomIndex : Fin blockCount)
    (semanticIDom :
      (reversePostOrder.get semanticIDomIndex).ImmediateDominatorInSSACFGRegion
        (reversePostOrder.get blockIndex) region irCtx) :
    value.get? blockIndex.val = some semanticIDomIndex.val := by
  obtain ⟨parentIndex, parentEq⟩ := invariant.initialized blockIndex
  have parentIsSemantic := metadata.stableSweep_parent_eq_immediateDominator
    complete represented invariant notNeeded blockIndex parentIndex semanticIDomIndex
    parentEq semanticIDom
  subst parentIndex
  exact parentEq

/-- End-to-end correctness for a stable CHK state over the concrete verified-region metadata. -/
theorem collectMetadata_stableSweep_correct
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (root : OperationPtr)
    (ctxVerified : irCtx.Verified root)
    (regionInBounds : region.InBounds irCtx.raw)
    (entry : BlockPtr)
    (entryEq : (region.get! irCtx.raw).firstBlock = some entry) :
    let metadata := DominanceAnalysis.collectMetadata region irCtx
    ∀ (value : DominanceValue metadata.reversePostOrder.size),
      SolverInvariantForRegion value
          (regionDominanceReversePostOrder metadata) region irCtx →
      (DominanceAnalysis.sweep metadata.predecessors value).needsSweep = false →
      ∀ (blockIndex semanticIDomIndex : Fin metadata.reversePostOrder.size),
        (metadata.reversePostOrder[semanticIDomIndex.val]).ImmediateDominatorInSSACFGRegion
            metadata.reversePostOrder[blockIndex.val] region irCtx →
          value.get? blockIndex.val = some semanticIDomIndex.val := by
  let metadata := DominanceAnalysis.collectMetadata region irCtx
  obtain ⟨nonempty, metadataCorrect, complete, represented⟩ :=
    collectMetadata_solverContracts region irCtx root ctxVerified regionInBounds entry entryEq
  letI : NeZero metadata.reversePostOrder.size := ⟨nonempty⟩
  dsimp only
  intro value invariant notNeeded blockIndex semanticIDomIndex semanticIDom
  apply metadataCorrect.stableSweep_correct complete represented invariant notNeeded
    blockIndex semanticIDomIndex
  simpa only [regionDominanceReversePostOrder_get] using semanticIDom

/--
End-to-end correctness when the concrete region reaches stability in its very
first executable CHK sweep.
-/
theorem collectMetadata_initial_stableSweep_correct
    (region : RegionPtr)
    (irCtx : WfIRContext OpCode)
    (root : OperationPtr)
    (ctxVerified : irCtx.Verified root)
    (regionInBounds : region.InBounds irCtx.raw)
    (entry : BlockPtr)
    (entryEq : (region.get! irCtx.raw).firstBlock = some entry) :
    let metadata := DominanceAnalysis.collectMetadata region irCtx
    (DominanceAnalysis.sweep metadata.predecessors
      (initial metadata.reversePostOrder.size)).needsSweep = false →
    ∀ (blockIndex semanticIDomIndex : Fin metadata.reversePostOrder.size),
      (metadata.reversePostOrder[semanticIDomIndex.val]).ImmediateDominatorInSSACFGRegion
          metadata.reversePostOrder[blockIndex.val] region irCtx →
        (DominanceAnalysis.sweep metadata.predecessors
          (initial metadata.reversePostOrder.size)).latticeElement.get?
            blockIndex.val = some semanticIDomIndex.val := by
  let metadata := DominanceAnalysis.collectMetadata region irCtx
  obtain ⟨nonempty, metadataCorrect, complete, represented⟩ :=
    collectMetadata_solverContracts region irCtx root ctxVerified regionInBounds entry entryEq
  letI : NeZero metadata.reversePostOrder.size := ⟨nonempty⟩
  dsimp only
  intro notNeeded blockIndex semanticIDomIndex semanticIDom
  apply metadataCorrect.initial_stableSweep_correct complete represented notNeeded
    blockIndex semanticIDomIndex
  simpa only [regionDominanceReversePostOrder_get] using semanticIDom

/--
The public immediate-dominator query exposes the semantic immediate dominator
stored in a stable, certified region fact.
-/
theorem BlockPtr.immediateDominator?_eq_of_stable_region_fact
    (block regionBlock : BlockPtr)
    (region : RegionPtr)
    (dfCtx : DataFlowContext)
    (irCtx : WfIRContext OpCode)
    (fact : RegionDominanceFact)
    (factEq : region.getRegionDominanceFact? dfCtx irCtx = some fact)
    (nonempty : fact.payload.metadata.reversePostOrder.size ≠ 0)
    (metadata : @RegionDominanceMetadataCorrectForRegion OpCode inferInstance
      fact.payload.metadata region irCtx ⟨nonempty⟩)
    (complete : PredecessorTableCompleteForRegion
      (regionDominanceReversePostOrder fact.payload.metadata)
      fact.payload.metadata.predecessors irCtx)
    (represented : ReachableBlocksRepresented
      (regionDominanceReversePostOrder fact.payload.metadata) region irCtx)
    (invariant : SolverInvariantForRegion fact.payload.latticeElement
      (regionDominanceReversePostOrder fact.payload.metadata) region irCtx)
    (notNeeded : (DominanceAnalysis.sweep fact.payload.metadata.predecessors
      fact.payload.latticeElement).needsSweep = false)
    (blockIndex semanticIDomIndex : Fin fact.payload.metadata.reversePostOrder.size)
    (blockEq : fact.payload.metadata.reversePostOrder[blockIndex.val] = block)
    (blockLookup : fact.payload.metadata.blockIndex.get? block = some blockIndex.val)
    (semanticIDom : regionBlock.ImmediateDominatorInSSACFGRegion block region irCtx)
    (semanticIDomEq :
      fact.payload.metadata.reversePostOrder[semanticIDomIndex.val] = regionBlock) :
    block.immediateDominator? dfCtx irCtx = some regionBlock := by
  letI : NeZero fact.payload.metadata.reversePostOrder.size := ⟨nonempty⟩
  have blockParent := metadata.blocks_parent blockIndex
  simp only [regionDominanceReversePostOrder_get, blockEq] at blockParent
  have semanticIDomIndexed :
      BlockPtr.ImmediateDominatorInSSACFGRegion
        ((regionDominanceReversePostOrder fact.payload.metadata).get semanticIDomIndex)
        ((regionDominanceReversePostOrder fact.payload.metadata).get blockIndex) region irCtx := by
    simpa only [regionDominanceReversePostOrder_get, semanticIDomEq, blockEq]
      using semanticIDom
  have stored := metadata.stableSweep_correct complete represented invariant notNeeded
    blockIndex semanticIDomIndex semanticIDomIndexed
  unfold BlockPtr.immediateDominator?
  simp [blockParent, factEq, Fact.blockIndex, Fact.dominanceValue, Fact.reversePostOrder]
  change (fact.payload.metadata.blockIndex.get? block >>= fun foundBlockIndex =>
    fact.payload.latticeElement.get? foundBlockIndex >>= fun immediateDominatorIndex =>
      fact.payload.metadata.reversePostOrder[immediateDominatorIndex]?) = some regionBlock
  rw [blockLookup]
  change (fact.payload.latticeElement.get? blockIndex.val >>= fun immediateDominatorIndex =>
    fact.payload.metadata.reversePostOrder[immediateDominatorIndex]?) = some regionBlock
  rw [stored]
  change fact.payload.metadata.reversePostOrder[semanticIDomIndex.val]? = some regionBlock
  rw [Array.getElem?_eq_getElem semanticIDomIndex.isLt, semanticIDomEq]

/-- `intersect` produces an RPO bound that still contains every shared semantic dominator. -/
theorem WorkingForestForRegion.le_intersect_of_dominates [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (ordered : OrderedForRegion reversePostOrder region irCtx)
    (dominatorIndex index1 index2 : Fin blockCount)
    (initialized1 : Initialized value index1)
    (initialized2 : Initialized value index2)
    (dominates1 : (reversePostOrder.get dominatorIndex).DominatesInSSACFGRegion
      (reversePostOrder.get index1) region irCtx)
    (dominates2 : (reversePostOrder.get dominatorIndex).DominatesInSSACFGRegion
      (reversePostOrder.get index2) region irCtx) :
    dominatorIndex.val ≤ value.intersect index1.val index2.val := by
  obtain ⟨result, hresult, _, dominates⟩ :=
    forest.intersect_preserves_dominator ordered dominatorIndex index1 index2
      initialized1 initialized2 dominates1 dominates2
  rw [hresult]
  exact ordered dominatorIndex result dominates

/--
Intersecting two initialized predecessors retains their target block's
semantic immediate dominator.
-/
theorem WorkingForestForRegion.le_intersect_predecessors [HasOpInfo OpInfo]
    {value : DominanceValue blockCount}
    {reversePostOrder : Vector BlockPtr blockCount}
    {region : RegionPtr}
    {irCtx : WfIRContext OpInfo}
    (forest : WorkingForestForRegion value reversePostOrder region irCtx)
    (ordered : OrderedForRegion reversePostOrder region irCtx)
    (blockIndex dominatorIndex predecessor1 predecessor2 : Fin blockCount)
    (semanticIDom :
      (reversePostOrder.get dominatorIndex).ImmediateDominatorInSSACFGRegion
        (reversePostOrder.get blockIndex) region irCtx)
    (predecessor1Parent :
      ((reversePostOrder.get predecessor1).get! irCtx.raw).parent = some region)
    (predecessor2Parent :
      ((reversePostOrder.get predecessor2).get! irCtx.raw).parent = some region)
    (edge1 : reversePostOrder.get blockIndex ∈
      (reversePostOrder.get predecessor1).getSuccessors! irCtx.raw)
    (edge2 : reversePostOrder.get blockIndex ∈
      (reversePostOrder.get predecessor2).getSuccessors! irCtx.raw)
    (initialized1 : Initialized value predecessor1)
    (initialized2 : Initialized value predecessor2) :
    dominatorIndex.val ≤ value.intersect predecessor1.val predecessor2.val := by
  unfold BlockPtr.ImmediateDominatorInSSACFGRegion at semanticIDom
  have dominates1 := semanticIDom.1.dominates_predecessor predecessor1Parent edge1
  have dominates2 := semanticIDom.1.dominates_predecessor predecessor2Parent edge2
  exact forest.le_intersect_of_dominates ordered dominatorIndex predecessor1 predecessor2
    initialized1 initialized2 dominates1 dominates2

end DominanceValue

end Veir
