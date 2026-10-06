import WeakNullstellensatz.Finitesatz
import WeakNullstellensatz.ManyValuedLogic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Monad

open MvPolynomial

namespace MvPolynomial

theorem eval_bind₁ {R σ τ : Type*} [CommSemiring R] (x : τ → R)
    (g : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    eval x (bind₁ g p) = eval (fun i => eval x (g i)) p :=
  eval₂Hom_bind₁ (RingHom.id R) x g p

end MvPolynomial

variable {Op Truth Atom K : Type*} [Signature Op] [Field K]

structure SymbolTraslation (e : Truth ↪ K) (M : LogicalMatrix Op Truth) where
  translator : (o : Op) → MvPolynomial (Fin $ Signature.arity o) K
  eval_translator : ∀ (o : Op) (xs : Fin (Signature.arity o) → Truth),
    eval (fun i => e (xs i)) (translator o) = e (M.interp o xs)

namespace SymbolTraslation

variable {e : Truth ↪ K} {M : LogicalMatrix Op Truth}

instance : CoeFun (SymbolTraslation e M)
    (fun _ => (o : Op) → MvPolynomial (Fin $ Signature.arity o) K) :=
  ⟨SymbolTraslation.translator⟩

attribute [coe] SymbolTraslation.translator

noncomputable def translate (T : SymbolTraslation e M) :
    Formula Atom Op → MvPolynomial Atom K
  | .var a => X a
  |.oper o args => bind₁ (fun i => T.translate (args i)) (T o)

theorem eval_translate (v : Atom → Truth) (φ : Formula Atom Op) (T : SymbolTraslation e M) :
    eval (fun a => e (v a)) (T.translate φ) = e (M.eval v φ) := by
  induction φ with
  | var a =>
    simp [translate, LogicalMatrix.eval]
  | oper o args ih =>
    simp only [translate, LogicalMatrix.eval, eval_bind₁, ih]
    exact T.eval_translator o _

end SymbolTraslation
