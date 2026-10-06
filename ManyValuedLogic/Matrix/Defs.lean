import Mathlib.Data.Set.Basic
import ManyValuedLogic.Formula

namespace ManyValuedLogic

structure LogicalMatrix (S : Signature) (Truth : Type*) where
  interp      : (o : S) → (Fin o.arity → Truth) → Truth
  designated  : Set Truth

namespace LogicalMatrix

variable {Atom Truth : Type*} {S : Signature} (M : LogicalMatrix S Truth)

instance : CoeFun (LogicalMatrix S Truth)
    (fun _ => (o : S) → (Fin o.arity → Truth) → Truth) :=
  ⟨LogicalMatrix.interp⟩

attribute [coe] LogicalMatrix.interp

def eval (M : LogicalMatrix S Truth) (v : Atom → Truth) :
    Formula S Atom → Truth
  | .var a        => v a
  | .oper o args  => M o (fun i => M.eval v (args i))

lemma eval_subst (σ : Atom → Formula S Atom) (v : Atom → Truth) (φ : Formula S Atom) :
    M.eval v (φ.subst σ) = M.eval (fun a => M.eval v (σ a)) φ := by
  induction φ with
  | var a => rfl
  | oper o args ih => simp only [Formula.subst, eval, ih]

end LogicalMatrix

end ManyValuedLogic
