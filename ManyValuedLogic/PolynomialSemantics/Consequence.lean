import ManyValuedLogic.Algebra.Finitesatz
import ManyValuedLogic.PolynomialSemantics.Translation

open MvPolynomial

namespace ManyValuedLogic

variable {K σ : Type*} [Field K]

def polyConsequence
    (A : Set K) (P : Set (MvPolynomial σ K)) (f : MvPolynomial σ K) :
    Prop :=
  ∀ x : σ → K, (∀ i, x i ∈ A) → (∀ p ∈ P, aeval x p = 0) → aeval x f = 0

theorem polyConsequence_iff_span (A : Set K) (P : Set (MvPolynomial σ K))
  (f : MvPolynomial σ K) :
  polyConsequence A P f ↔ polyConsequence A (Ideal.span P : Set _) f := by
  simp only [polyConsequence]
  constructor
  . intro h x hx hP
    apply h x hx
    intro p hp
    refine hP p ?_
    exact Submodule.mem_span_of_mem hp
  . intro h x hx hP
    apply h x hx
    simp
    intro p hp
    induction hp using Submodule.span_induction with
    | zero => rfl
    | mem p' hp' => exact hP p' hp'
    | add p₁ p₂ hp₁ hp₂ ih₁ ih₂ => simp [ih₁, ih₂]
    | smul p₁ p₂ hp₂ ih => simp [ih]

section FinConsequence

variable [Fintype σ] (A : Finset K) (P : Set (MvPolynomial σ K))
  (f : MvPolynomial σ K)

theorem polyConsequence_iff_mem_vanishingIdeal :
    polyConsequence A P f ↔
      f ∈ vanishingIdeal K (zeroLocusOn (fun _ => A) (Ideal.span P) : Set (σ → K)) := by
  rw [mem_vanishingIdeal_iff, polyConsequence_iff_span, polyConsequence]
  simp

theorem polyConsequence_iff_mem_span_add :
    polyConsequence A P f ↔
        f ∈ Ideal.span P + vanishingIdeal K {x | ∀ i, x i ∈ A} := by
    rw [polyConsequence_iff_mem_vanishingIdeal]
    rw [vanishingIdeal_zeroLocus_eq_ideal_sum]

end FinConsequence

end ManyValuedLogic
