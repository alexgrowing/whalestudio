import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne

noncomputable section

open WittVector Ideal Matrix GlobalTheory.Sandwich TensorProduct

namespace GlobalTheory.DetInv

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

def IsDetElt (ε : PreTilt O p) (ψ : RL p O Λ →+* RL p O Λ) (N : ℕ) (Δ : RL p O Λ) : Prop :=
  Δ ∣ (inA (mu ε) : RL p O Λ) ^ N ∧ ∃ g, Δ = g * ψ Δ ∧ g ∣ (inA (xi ε) : RL p O Λ) ^ N

def HasOrders (C : Type) [Field C] [Algebra O C] (ε : PreTilt O p) (N : ℕ) (Δ : RL p O Λ)
    (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C) : Prop :=
  ∀ σ f, IsTheta σ f →
    a σ ≤ N ∧ c σ ≠ 0 ∧ Lead ((algebraMap O C).comp f) (inA (xi ε)) Δ (a σ) (c σ)

def IsIsom (C : Type) [Field C] [Algebra O C] (v : Valuation C NNReal) (γ : O ≃+* O) : Prop :=
  ∃ γC : C ≃+* C, (∀ x, γC (algebraMap O C x) = algebraMap O C (γ x)) ∧ ∀ z, v (γC z) = v z

end GlobalTheory.DetInv
