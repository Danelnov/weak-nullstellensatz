import WeakNullstellensatz.Finitesatz
import WeakNullstellensatz.ManyValuedLogic
import Mathlib.RingTheory.Nullstellensatz

open MvPolynomial

variable {F K σ : Type*} [Field K] [Fintype σ]

def MvPolynomial.consequence
    (A : σ → Finset K) (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) : Prop :=
  f ∈ (vanishingIdeal K (SetLike.coe $ zeroLocus_on A I))

variable (D A : Finset K)

def logic_poly_consequence
    (t : F → MvPolynomial σ K) (Γ : Finset F) (φ : F) : Prop :=
  MvPolynomial.consequence
    (fun _ : σ => A)
    (Ideal.span {∏ d ∈ D, (t γ - C d) | γ ∈ Γ})
    (t φ)
