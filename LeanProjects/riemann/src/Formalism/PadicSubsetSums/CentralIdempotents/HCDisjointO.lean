import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent

open Polynomial CategoryTheory
noncomputable section
namespace Formalism.IrreducibleCountingLemmas.TYPES

section Reps

variable {Γ : Type} [Group Γ]

def RepIso {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W) : Prop :=
  ∃ e : V ≃ₗ[ℂ] W, ∀ γ v, e (ρ γ v) = ρ' γ (e v)

end Reps

section Props

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : LabelConv K}

def TranspO (O : LabelMap K C) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (ρ : FDRep ℂ (GL ι K)),
    (Simple ρ → Simple (transp e ρ)) ∧ ∀ f, HasLabelO O ρ f → HasLabelO O (transp e ρ) f

def HCDisjointO (O : LabelMap K C) : Prop :=
  ∀ (n : ℕ) (b : Fin n → Fin 2) (τ τ₁ : ∀ c : Fin 2, FDRep ℂ (GL {i // b i = c} K)) (f : Fin 2 → K[X]),
    Function.Surjective b →
    (∀ c, Simple (τ c) ∧ Simple (τ₁ c) ∧ HasLabelO O (τ c) (f c) ∧ HasLabelO O (τ₁ c) (f c)) →
    IsCoprime (f 0) (f 1) →
    (∃ σ : FDRep ℂ (GL (Fin n) K), Simple σ ∧ RepIso σ.ρ (hcRep K b τ)) ∧
    (RepIso (hcRep K b τ) (hcRep K b τ₁) → ∀ c, RepIso (τ c).ρ (τ₁ c).ρ)

end Props

end Formalism.IrreducibleCountingLemmas.TYPES
