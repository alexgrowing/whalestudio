import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm

noncomputable section

def ChartBergmanBound.Statement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (ψ ρ : (Fin D → ℂ) → ℝ) (y₀ : Fin D → ℂ), IsOpen U → y₀ ∈ U →
    ContDiffOn ℝ 2 ψ U → ContinuousOn ρ U → 0 < ρ y₀ → (∀ w, 0 ≤ levi ψ y₀ w) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ F : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ F U →
      ENNReal.ofReal (‖F y₀‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y₀)) ≤
        ENNReal.ofReal (((((1 / Real.pi : ℝ) : ℂ) • hessC ψ y₀).det.re / ρ y₀ + ε) *
            (n : ℝ) ^ D) *
          ∫⁻ y in U, ENNReal.ofReal (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ρ y)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
