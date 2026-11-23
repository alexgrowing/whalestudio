import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftGraphMetric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def LiftGraphFactor.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a r : ℕ) (v : Fin r → Ω),
    (∀ j, v j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) v →
    ∃ Φ : ((Σ k, ι k) → ℂ) → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} ∧
      (∀ w : (Σ k, ι k) → ℂ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → 0 < Φ w) ∧
      (∀ (c : K → ℂ) (w : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) →
        Φ (fun p => c p.1 * w p) = (∏ k, ‖c k‖ ^ ((a • N.a) k)) ^ 2 * Φ w) ∧
      (∀ w : (Σ k, ι k) → ℂ, Φ (fun p => (starRingEnd ℂ) (w p)) = Φ w) ∧
      (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin r,
        secNormAt y N a (v j) (basePart₂ z) * N.h (basePart₂ z) ^ a * Real.sqrt (∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2) =
          ‖z ⟨none, j⟩‖ * Real.sqrt (Φ (basePart₂ z))) ∧
      (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ ξ : (Σ k, addIdx ι r k) → ℂ,
        IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z ξ →
        leviForm (fun z => Real.log (Φ (basePart₂ z))) z ξ =
          leviForm (fun z : (Σ k, addIdx ι r k) → ℂ => Real.log (∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2)) z ξ)

end

end GroundTheory.Heights₂.Heights.Targets
