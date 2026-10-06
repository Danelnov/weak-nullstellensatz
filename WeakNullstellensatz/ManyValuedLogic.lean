import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

/-- A signature takes a term of a certain type and assigns it an arity. -/
class Signature Op where
  arity : Op → Nat

inductive Formula (Atom Op : Type*) [Signature Op] where
  | var : Atom → Formula Atom Op
  | oper : (o : Op) → (Fin (Signature.arity o) → Formula Atom Op) → Formula Atom Op

namespace Formula
variable {Atom Op : Type*} [Signature Op]

def subst (σ : Atom → Formula Atom Op) : Formula Atom Op → Formula Atom Op
  | var a       => σ a
  | oper o args => oper o (fun i => (args i).subst σ)

end Formula

structure PropositionalLogic (Form : Type*) where
  consequence : Set Form → Form → Prop
  refl : ∀ {Γ φ}, φ ∈ Γ → consequence Γ φ
  mono : ∀ {Γ Δ φ}, consequence Γ φ → Γ ⊆ Δ → consequence Δ φ
  cut : ∀ {Γ Δ ψ}, (∀ δ ∈ Δ, consequence Γ δ) → consequence Δ ψ → consequence Γ ψ

def PropositionalLogic.Finitary {Form : Type*}
    (L : PropositionalLogic Form) : Prop :=
  ∀ {Γ φ}, L.consequence Γ φ →
    ∃ Δ : Finset Form, ↑Δ ⊆ Γ ∧ L.consequence Δ φ

structure LogicalMatrix (Op : Type*) [Signature Op] (Truth : Type*) where
  interp      : (o : Op) → (Fin (Signature.arity o) → Truth) → Truth
  designated  : Set Truth

namespace LogicalMatrix

variable {Atom Op Truth : Type*} [Signature Op] (M : LogicalMatrix Op Truth)

instance : CoeFun (LogicalMatrix Op Truth)
    (fun _ => (o : Op) → (Fin (Signature.arity o) → Truth) → Truth) :=
  ⟨LogicalMatrix.interp⟩

attribute [coe] LogicalMatrix.interp

def eval (M : LogicalMatrix Op Truth) (v : Atom → Truth) :
    Formula Atom Op → Truth
  | .var a        => v a
  | .oper o args  => M o (fun i => M.eval v (args i))

lemma eval_subst (σ : Atom → Formula Atom Op) (v : Atom → Truth)
    (φ : Formula Atom Op) :
    M.eval v (φ.subst σ) = M.eval (fun a => M.eval v (σ a)) φ := by
  induction φ with
  | var a => rfl
  | oper o args ih => simp only [Formula.subst, eval, ih]

section consequence

variable {Γ Δ : Set (Formula Atom Op)} {φ : Formula Atom Op}

variable (Γ φ) in
def consequence : Prop :=
  ∀ v : Atom → Truth, M.eval v '' Γ ⊆ M.designated → M.eval v φ ∈ M.designated

def consequence_of_mem  (h : φ ∈ Γ) : M.consequence Γ φ :=
  fun _ hv => hv (Set.mem_image_of_mem _ h)

def consequence_mono (h : M.consequence Γ φ) (h1 : Γ ⊆ Δ) : M.consequence Δ φ :=
  fun v hv => h v ((Set.image_mono h1).trans hv)

def consequence_cut (hΔΓ : ∀ δ ∈ Δ, M.consequence Γ δ) (hΔ : M.consequence Δ φ) :
    M.consequence Γ φ := by
  rw [consequence] at *
  intro v hv
  apply hΔ v
  rintro a ⟨δ, hδ, rfl⟩
  specialize hΔΓ δ hδ
  rw [consequence] at hΔΓ
  exact hΔΓ v hv

def consequence_structural (σ : Atom → Formula Atom Op) (h : M.consequence Γ φ) :
    M.consequence (Formula.subst σ '' Γ) (φ.subst σ) := by
  rw [consequence] at *
  intro v hv
  rw [eval_subst]
  refine h _ ?_
  clear h
  rintro a ⟨γ, hγ, rfl⟩
  have key := hv (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hγ))
  rwa [eval_subst] at key

end consequence

def toLogic (Atom : Type*) : PropositionalLogic (Formula Atom Op) where
  consequence := M.consequence
  refl := M.consequence_of_mem
  mono := M.consequence_mono
  cut := M.consequence_cut

@[simp] theorem toLogic_consequence (Atom : Type*) :
  (M.toLogic Atom).consequence = M.consequence := rfl

end LogicalMatrix
