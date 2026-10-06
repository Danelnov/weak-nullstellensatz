import Mathlib.Data.Finset.Basic

namespace ManyValuedLogic

class PropositionalLogic {Form : Type*} (cons : Set Form → Form → Prop) : Prop where
  refl : ∀ {Γ φ}, φ ∈ Γ → cons Γ φ
  mono : ∀ {Γ Δ φ}, cons Γ φ → Γ ⊆ Δ → cons Δ φ
  cut : ∀ {Γ Δ ψ}, (∀ δ ∈ Δ, cons Γ δ) → cons Δ ψ → cons Γ ψ

class FinitaryLogic {Form : Type*} (cons : Set Form → Form → Prop)
    [PropositionalLogic cons] : Prop where
  finitary : ∀ {Γ φ}, cons Γ φ → ∃ Δ : Finset Form, ↑Δ ⊆ Γ ∧ cons Δ φ

end ManyValuedLogic
