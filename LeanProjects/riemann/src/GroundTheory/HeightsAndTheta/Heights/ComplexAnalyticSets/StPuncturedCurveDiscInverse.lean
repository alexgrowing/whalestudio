import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchNormalisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PuncturedCurveDiscInverse.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    ∃ ε > 0, ∀ (φ : ℂ → Fin n → ℂ) (σ₀ : ℂ) (δ : ℝ), 0 < δ →
      DifferentiableOn ℂ φ (Metric.ball σ₀ δ) → Set.InjOn φ (Metric.ball σ₀ δ) →
      Set.MapsTo φ (Metric.ball σ₀ δ) (zeroSet I) → φ σ₀ ∈ Metric.ball q ε → φ σ₀ ≠ q →
      ∃ U : Set (Fin n → ℂ), IsOpen U ∧ φ σ₀ ∈ U ∧ ∃ ψ : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ ψ U ∧
        ∀ z ∈ zeroSet I ∩ U, ∃ σ ∈ Metric.ball σ₀ δ, φ σ = z ∧ ψ z = σ

end

end GroundTheory.Heights₂.Heights
