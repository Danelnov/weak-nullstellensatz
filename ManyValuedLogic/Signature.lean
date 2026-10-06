universe u

namespace ManyValuedLogic

/-- A signature takes a term of a certain type and assigns it an arity. -/
structure Signature where
  Op : Type u
  arity : Op → Nat

namespace Signature

attribute [coe] Signature.Op

instance : CoeSort Signature.{u} (Type u) := ⟨Signature.Op⟩

abbrev Op.arity {S : Signature.{u}} (o : S) : Nat := S.arity o

end Signature

end ManyValuedLogic
