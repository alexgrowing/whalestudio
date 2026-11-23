import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaCharacteristicZeroNorm

open Complex GlobalTheory.Glob.IntegralWittCoefficients

def thetaChar (a b : Fin 2) (z τ : ℂ) : ℂ :=
  cexp ((Real.pi : ℂ) * I * ((a : ℕ) : ℂ) ^ 2 * τ / 4 +
      (Real.pi : ℂ) * I * ((a : ℕ) : ℂ) * (z + ((b : ℕ) : ℂ) / 2)) *
    jacobiTheta₂ (z + (((a : ℕ) : ℂ) * τ + ((b : ℕ) : ℂ)) / 2) τ

def IsEvenChar (c : Fin 2 × Fin 2) : Prop := c ≠ (1, 1)

def IsLatticeOf (Λ : AddSubgroup ℂ) (ω₁ τ : ℂ) : Prop :=
  ∀ w : ℂ, w ∈ Λ ↔ ∃ m n : ℤ, w = ω₁ * ((m : ℂ) + (n : ℂ) * τ)

def ThetaZeroNorm : Prop :=
  ∀ (Λ : AddSubgroup ℂ) (ω₁ τ t₀ : ℂ), ω₁ ≠ 0 → 0 < τ.im → IsLatticeOf Λ ω₁ τ →
    t₀ ∉ Λ → 2 * t₀ ∈ Λ →
      (∃! c : Fin 2 × Fin 2, IsEvenChar c ∧ thetaChar c.1 c.2 (t₀ / ω₁) τ = 0) ∧
      ∀ c : Fin 2 × Fin 2, IsEvenChar c → thetaChar c.1 c.2 (t₀ / ω₁) τ = 0 →
        0 < normSq1 Λ (th0 Λ t₀) ∧
        (normSq1 Λ (th0 Λ t₀))⁻¹ = Real.sqrt (2 * τ.im) * ‖thetaChar c.1 c.2 0 τ‖ ^ 2

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaCharacteristicZeroNorm
