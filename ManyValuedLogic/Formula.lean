import ManyValuedLogic.Signature

universe u v

namespace ManyValuedLogic

inductive Formula (S : Signature.{u}) (Atom : Type v) where
  | var : Atom → Formula S Atom
  | oper (o : S) : (Fin o.arity → Formula S Atom) → Formula S Atom

namespace Formula

variable {S : Signature.{u}} {Atom : Type v}

def subst (σ : Atom → Formula S Atom) : Formula S Atom → Formula S Atom
  | var a       => σ a
  | oper o args => oper o (fun i => (args i).subst σ)

end Formula

end ManyValuedLogic
