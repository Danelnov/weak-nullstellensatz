import ManyValuedLogic.PolynomialSemantics.Consequence
import ManyValuedLogic.PolynomialSemantics.Translation
import ManyValuedLogic.Matrix.Consequence

import Mathlib.Algebra.MvPolynomial.Basic

open MvPolynomial

namespace ManyValuedLogic

variable {Atom Truth K : Type*} {S : Signature} [Field K]
  {M : LogicalMatrix S Truth} {e : Truth ↪ K} (T : SymbolTranslation e M)

noncomputable def SymbolTranslation.translateD (hD : M.designated.Finite)
    (φ : Formula S Atom) : MvPolynomial Atom K :=
  ∏ d ∈ hD.toFinset, (T.translate φ - C (e d))

theorem SymbolTranslation.eval_translateD_eq_zero_iff (hD : M.designated.Finite)
    (v : Atom → Truth) (φ : Formula S Atom) :
    eval (fun a => e (v a)) (T.translateD hD φ) = 0 ↔
      M.eval v φ ∈ M.designated := by
  simp [translateD, Finset.prod_eq_zero_iff, sub_eq_zero, eval_translate]

omit [Field K] in
/-- A point all of whose coordinates lie in the range of `e` is of the form `e ∘ v`. -/
private lemma exists_eq_comp_of_forall_mem_range {x : Atom → K}
    (hx : ∀ a, x a ∈ Set.range e) :
    ∃ v : Atom → Truth, (fun a => e (v a)) = x :=
  ⟨fun a => (hx a).choose, funext fun a => (hx a).choose_spec⟩

theorem consequence_iff_polyConsequence (hD : M.designated.Finite)
    (Γ : Set (Formula S Atom)) (φ : Formula S Atom) :
    M.consequence Γ φ ↔
      polyConsequence (Set.range e) (T.translateD hD '' Γ) (T.translateD hD φ) := by
  simp only [polyConsequence, Set.forall_mem_image]
  constructor
  · intro hM x hx hΓ
    obtain ⟨v, rfl⟩ := exists_eq_comp_of_forall_mem_range hx
    refine (T.eval_translateD_eq_zero_iff hD v φ).2 (hM v ?_)
    rintro _ ⟨γ, hγ, rfl⟩
    exact (T.eval_translateD_eq_zero_iff hD v γ).1 (hΓ hγ)
  · intro h v hv
    refine (T.eval_translateD_eq_zero_iff hD v φ).1 (h _ (fun a => ⟨v a, rfl⟩) fun γ hγ => ?_)
    exact (T.eval_translateD_eq_zero_iff hD v γ).2 (hv ⟨γ, hγ, rfl⟩)

end ManyValuedLogic
