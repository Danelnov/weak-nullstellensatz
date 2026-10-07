import ManyValuedLogic.Algebra.Finitesatz
import ManyValuedLogic.Logic

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

variable (A : Set K) {P Q : Set (MvPolynomial σ K)} {f g : MvPolynomial σ K}

private theorem consequence_of_mem (h : f ∈ P) : polyConsequence A P f := by
  intro x hx hp
  exact hp f h

private theorem consequence_mono (h : polyConsequence A P f) (h1 : P ⊆ Q) :
    polyConsequence A Q f := by
  intro x hx hq
  apply h x hx
  intro p hp
  exact hq p (Set.mem_of_subset_of_mem h1 hp)

private theorem consequence_cut
    (hQP : ∀ q ∈ Q, polyConsequence A P q) (hf : polyConsequence A Q f) :
    polyConsequence A P f := by
  intro x hx hp
  apply hf x hx
  intro q hq
  exact hQP q hq x hx hp

instance (A : Set K) : PropositionalLogic (polyConsequence (σ := σ) A) where
  refl := consequence_of_mem A
  mono := consequence_mono A
  cut := consequence_cut A

end ManyValuedLogic
