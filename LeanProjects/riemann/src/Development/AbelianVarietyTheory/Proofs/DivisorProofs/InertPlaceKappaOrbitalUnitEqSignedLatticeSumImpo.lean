import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

noncomputable section

namespace GlobalTheory.InertUnitOrb

open GlobalTheory.UnitLemma Matrix

def stdH (K : UQ) (n : ℕ) (y z : Fin n → K.E) : K.E := ∑ k, y k * K.c (z k)

def IsModel {K : UQ} (B : InvAlg K) {n : ℕ} (γ : Matrix (Fin n) (Fin n) K.E) (x : B.Aˣ)
    (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) : Prop :=
  B.σ (x : B.A) = x ∧ (∀ y, ψ (B.g * y) = γ *ᵥ ψ y) ∧ ∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z

end GlobalTheory.InertUnitOrb
