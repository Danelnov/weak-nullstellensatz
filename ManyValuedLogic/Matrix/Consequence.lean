import Mathlib.Data.Set.Basic
import ManyValuedLogic.Matrix.Defs
import ManyValuedLogic.Logic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace ManyValuedLogic

namespace LogicalMatrix

variable {Atom Truth : Type*} {S : Signature} (M : LogicalMatrix S Truth)
  {Γ Δ : Set (Formula S Atom)} {φ : Formula S Atom}

variable (Γ φ) in
def consequence : Prop :=
  ∀ v : Atom → Truth, M.eval v '' Γ ⊆ M.designated → M.eval v φ ∈ M.designated

private theorem consequence_of_mem  (h : φ ∈ Γ) : M.consequence Γ φ :=
  fun _ hv => hv (Set.mem_image_of_mem _ h)

private theorem consequence_mono (h : M.consequence Γ φ) (h1 : Γ ⊆ Δ) : M.consequence Δ φ :=
  fun v hv => h v ((Set.image_mono h1).trans hv)

private theorem consequence_cut (hΔΓ : ∀ δ ∈ Δ, M.consequence Γ δ) (hΔ : M.consequence Δ φ) :
    M.consequence Γ φ := by
  rw [consequence] at *
  intro v hv
  apply hΔ v
  rintro a ⟨δ, hδ, rfl⟩
  specialize hΔΓ δ hδ
  rw [consequence] at hΔΓ
  exact hΔΓ v hv

private theorem consequence_structural (σ : Atom → Formula S Atom) (h : M.consequence Γ φ) :
    M.consequence (Formula.subst σ '' Γ) (φ.subst σ) := by
  rw [consequence] at *
  intro v hv
  rw [eval_subst]
  refine h _ ?_
  clear h
  rintro a ⟨γ, hγ, rfl⟩
  have key := hv (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hγ))
  rwa [eval_subst] at key

instance (M : LogicalMatrix S Truth) :
    PropositionalLogic (M.consequence (Atom := Atom)) where
  refl := M.consequence_of_mem
  mono := M.consequence_mono
  cut := M.consequence_cut

end LogicalMatrix

end ManyValuedLogic
