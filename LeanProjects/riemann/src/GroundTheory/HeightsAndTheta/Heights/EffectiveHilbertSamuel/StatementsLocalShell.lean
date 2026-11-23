import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.ObjectsExtDelta
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology

noncomputable section

def LocalShell.Statement : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ (V : Set (Fin D → ℂ)) (z₀ : Fin D → ℂ) (w : (Fin D → ℂ) → Fin D → ℂ)
    (F σ : (Fin D → ℂ) → ℝ), IsOpen V → z₀ ∈ V → AnalyticOnNhd ℂ w V → w z₀ = 0 →
    LinearMap.det (fderiv ℂ w z₀ : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) ≠ 0 →
    ContinuousOn F V → (∀ z ∈ V, 0 ≤ F z) → ContinuousOn σ V → (∀ z ∈ V, 0 < σ z) →
    (∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ z ∈ V, δ ≤ dist z z₀ → η ≤ (∑ i, ‖w z i‖ ^ 2) * σ z) →
    Tendsto (fun ε : ℝ => ∫⁻ z in V, ENNReal.ofReal (F z * (((∑ i, ‖w z i‖ ^ 2) * σ z) ^ D)⁻¹ *
        extShell ε ((∑ i, ‖w z i‖ ^ 2) * σ z)))
      (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (F z₀ / σ z₀ ^ D /
        ‖LinearMap.det (fderiv ℂ w z₀ : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 *
        (Real.pi ^ D / ((D - 1).factorial : ℝ)) * Real.log 2)))

end

end GroundTheory.Heights₂.Heights.EffectiveHS
