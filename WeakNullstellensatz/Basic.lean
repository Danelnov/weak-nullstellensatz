import Mathlib
import Mathlib.RingTheory.Ideal.Span


open MvPolynomial
open Ideal

variable {R σ : Type*} [CommRing R]


noncomputable def u_poly (i : σ) (A : Finset R) : MvPolynomial σ R :=
  ∏ a ∈ A, (X i - C a)

def ideal_U (A : Finset R) : Ideal (MvPolynomial σ R) :=
  Ideal.span (Set.range (λ i => u_poly i A))


lemma eval_u_poly {i : σ} {A : Finset R} (x : σ → R) (hxA : ∀ (i : σ), x i ∈ A) : (eval x) (u_poly i A) = 0 := by
  rw [u_poly]
  simp
  have ⟨a, ain, hx⟩: ∃ a ∈ A, x i = a := by aesop
  apply Finset.prod_eq_zero ain
  rw [hx, sub_self]


theorem mem_ideal_U_iff [Fintype σ] [IsDomain R] [DecidableEq σ] (A : Finset R) (f : MvPolynomial σ R) :
  f ∈ ideal_U A ↔ ∀ (x : σ → R), (∀ (i : σ), x i ∈ A) → f.eval x = 0 := by
  rw [ideal_U, mem_span_range_iff_exists_fun]
  constructor
  . intro h x hxA
    obtain ⟨g, hg⟩ := h
    simp [← hg]
    apply Finset.sum_eq_zero
    intro i hi
    rw [eval_u_poly, mul_zero]
    assumption
  . intro h
    by_cases hA : A = ∅
    . rcases isEmpty_or_nonempty σ with (h1 | h2) <;> simp_all +decide [u_poly]
      . rw [eq_C_of_isEmpty f] at h ⊢
        specialize h (fun _ => 0)
        simp_all +singlePass
      . obtain ⟨i⟩ := h2
        exists fun j => if j = i then f else 0
        simp_all +singlePass
    . have := combinatorial_nullstellensatz_exists_linearCombination
        (fun i => A) (fun i => Finset.nonempty_of_ne_empty hA) f h
      obtain ⟨g, h1, h2⟩ := this
      use g
      simp [u_poly]
      simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype] at h2
      exact h2.symm
