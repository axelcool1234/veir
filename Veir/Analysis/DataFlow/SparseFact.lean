module

public import Veir.Analysis.DataFlowFramework
public import Veir.Analysis.DataFlow.Domains.AbstractDomain

public section

namespace Veir

/--
Witnesses that the fact slot `kind` stores a sparse payload over `Domain`.

Rather than asserting a propositional type equality `FactPayload kind =
SparsePayload Domain` and `cast`ing across it, we carry an explicit isomorphism
together with its round-trip laws. For the common case where `FactPayload kind`
is *definitionally* `SparsePayload Domain` the instance is just `id`/`id` with
`rfl` laws (see `SparseConstantPropagation`), but unlike `cast` the laws below
rewrite cleanly under `simp`/`grind`, which keeps downstream correctness proofs
free of `cast`/`Eq.rec` juggling.
-/
class SparseFactSpec (kind : FactKind) (Domain : outParam Type) where
  /-- Inject a sparse payload into the fact slot's payload type. -/
  toPayload : SparsePayload Domain → FactPayload kind
  /-- Project the fact slot's payload type back to a sparse payload. -/
  ofPayload : FactPayload kind → SparsePayload Domain
  /-- `ofPayload` is a left inverse of `toPayload`. -/
  of_to (payload : SparsePayload Domain) : ofPayload (toPayload payload) = payload
  /-- `toPayload` is a left inverse of `ofPayload`. -/
  to_of (payload : FactPayload kind) : toPayload (ofPayload payload) = payload

namespace SparseFact

variable {kind : FactKind} {Domain : Type}
variable [SparseFactSpec kind Domain]

def getPayload (fact : Fact kind) : SparsePayload Domain :=
  SparseFactSpec.ofPayload fact.payload

def setPayload (fact : Fact kind) (payload : SparsePayload Domain) : Fact kind :=
  { fact with payload := SparseFactSpec.toPayload payload }

def latticeElement (fact : Fact kind) : Domain :=
  (getPayload fact).latticeElement

def setLatticeElement (fact : Fact kind) (latticeElement : Domain) : Fact kind :=
  let payload := getPayload fact
  setPayload fact { payload with latticeElement := latticeElement }

@[simp]
theorem getPayload_setPayload (fact : Fact kind) (payload : SparsePayload Domain) :
    getPayload (setPayload fact payload) = payload :=
  SparseFactSpec.of_to payload

@[simp]
theorem latticeElement_setLatticeElement (fact : Fact kind) (x : Domain) :
    latticeElement (setLatticeElement fact x) = x := by
  simp [latticeElement, setLatticeElement]

/--
Propagate a sparse lattice update by revisiting dependents and all users of the
updated SSA value for subscribed analyses.

This only ever enqueues work, so it is written to thread the `WorkList` and apply
it to `dfCtx` once at the end. That makes it manifest — and provable by `rfl`
(see `propagate_preserves_lattice`) — that propagation never touches the fact
store, which the soundness/termination proofs rely on.
-/
def propagate (state : Fact kind) (anchor : LatticeAnchor)
  (dfCtx : DataFlowContext) (irCtx : IRContext OpCode) : DataFlowContext := Id.run do
  let mut workList := state.enqueueDependents dfCtx.workList
  match anchor with
  | .ValuePtr ssaValue =>
    let mut maybeUse := ssaValue.getFirstUse! irCtx
    while let some use := maybeUse do
      let user := (use.get! irCtx).owner
      for analysisKind in state.subscribers do
        match InsertPoint.after? user irCtx with
        | some point =>
          workList := workList.enqueue (point, analysisKind)
        | none =>
          pure ()
      maybeUse := (use.get! irCtx).nextUse
  | _ =>
    pure ()
  { dfCtx with workList := workList }

/-- Propagation only enqueues work; it never changes the fact store. -/
@[simp] theorem propagate_preserves_lattice (state : Fact kind) (anchor : LatticeAnchor)
    (dfCtx : DataFlowContext) (irCtx : IRContext OpCode) :
    (propagate state anchor dfCtx irCtx).lattice = dfCtx.lattice := by
  unfold propagate
  cases anchor <;> rfl

section

variable [Bot Domain]

/-- Default sparse lattice fact for the given anchor. -/
def mkDefault : Fact kind :=
  { payload := SparseFactSpec.toPayload { latticeElement := ⊥ } }

instance : FactSpec kind where
  mkDefault := SparseFact.mkDefault (kind := kind)
  propagate := SparseFact.propagate (kind := kind)

end

def getElement? (kind : FactKind) [SparseFactSpec kind Domain] [FactSpec kind]
    (ssaValue : ValuePtr) (dfCtx : DataFlowContext) : Option Domain := do
  let state ← dfCtx.getFact? kind (.ValuePtr ssaValue)
  return latticeElement state

def getElementD (kind : FactKind) [SparseFactSpec kind Domain] [FactSpec kind]
    (ssaValue : ValuePtr) (fallback : Domain)
    (dfCtx : DataFlowContext) : Domain :=
  (getElement? kind ssaValue dfCtx).getD fallback

/-- `getElementD` depends only on the underlying `getFact?` read. -/
theorem getElementD_congr (kind : FactKind) [SparseFactSpec kind Domain] [FactSpec kind]
    (ssaValue : ValuePtr) (fallback : Domain) {ctx₁ ctx₂ : DataFlowContext}
    (h : ctx₁.getFact? kind (.ValuePtr ssaValue) = ctx₂.getFact? kind (.ValuePtr ssaValue)) :
    getElementD kind ssaValue fallback ctx₁ = getElementD kind ssaValue fallback ctx₂ := by
  simp only [getElementD, getElement?, h]

/-- When a fact is present, `getElementD` reads off its lattice element. -/
theorem getElementD_of_getFact? (kind : FactKind) [SparseFactSpec kind Domain] [FactSpec kind]
    (ssaValue : ValuePtr) (fallback : Domain) (dfCtx : DataFlowContext) (fact : Fact kind)
    (h : dfCtx.getFact? kind (.ValuePtr ssaValue) = some fact) :
    getElementD kind ssaValue fallback dfCtx = latticeElement fact := by
  simp [getElementD, getElement?, h]

end SparseFact

end Veir
