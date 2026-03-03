module

public import Veir.Analysis.DataFlow.SparseLatticeState
public import Veir.Data.LLVM.Int.Basic

public section

namespace Veir

structure KnownConstant where
  bitwidth : Nat
  value : Data.LLVM.Int bitwidth
deriving BEq

-- Constant domain
inductive ConstantDomain where
  | top
  | bottom
  | constant (value : KnownConstant)
deriving BEq, TypeName

namespace ConstantDomain

/-- Alias for the top element: value is unknown or conflicting. -/
def unknown : ConstantDomain :=
  .top

/-- Alias for the bottom element: no information has been learned yet. -/
def uninitialized : ConstantDomain :=
  .bottom

/-- Build a constant lattice element from an integer at the given bitwidth. -/
def ofInt (bitwidth : Nat) (value : Int) : ConstantDomain :=
  .constant { bitwidth := bitwidth
              value := .val (BitVec.ofInt bitwidth value) }

def join (lhs rhs : ConstantDomain) : ConstantDomain :=
    match lhs, rhs with
    | .bottom, x => x
    | x, .bottom => x
    | .top, _ => .top
    | _, .top => .top
    | .constant lhsVal, .constant rhsVal =>
      if lhsVal == rhsVal then
        .constant lhsVal
      else
        .top

def meet (lhs rhs : ConstantDomain) : ConstantDomain :=
    match lhs, rhs with
    | .top, x => x
    | x, .top => x
    | .bottom, _ => .bottom
    | _, .bottom => .bottom
    | .constant lhsVal, .constant rhsVal =>
      if lhsVal == rhsVal then
        .constant lhsVal
      else
        .bottom

end ConstantDomain

instance : LatticeElement ConstantDomain where
  typeNameInst := inferInstance
  bottom := .bottom
  top := .top
  join := .join
  meet := .meet

end Veir
