import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenOfPoincareLelongHyperplane
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff

noncomputable section

def PolydiscLelongLimit.Statement : Prop :=
  ∀ (d m : ℕ) (r ρ : ℝ) (F : (Fin (d + 1) → ℂ) → ℂ) (χ : (Fin (d + 1) → ℂ) → ℝ)
    (ψ : Fin d → (Fin (d + 1) → ℂ) → ℝ),
    ρ < r → VanishesToOrder F r m → ContDiffOn ℝ ∞ χ (Metric.ball 0 r) →
    (∀ τ ∈ Metric.ball (0 : Fin (d + 1) → ℂ) r, χ τ ≠ 0 → τ ∈ Metric.ball 0 ρ) →
    (∀ k, ContDiffOn ℝ ∞ (ψ k) (Metric.ball 0 r)) →
      Tendsto (fun ε : ℝ =>
          ReciprocityTheory.AnForm.maInt (vecCons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) χ (Metric.ball 0 r))
        (𝓝[>] 0)
        (𝓝 ((m : ℝ) * ∫ w in Metric.ball (0 : Fin d → ℂ) r,
          χ (ReciprocityTheory.AnForm.A.hypIncl w) * ReciprocityTheory.AnForm.A.densHyp ψ w))

end

end GroundTheory.Heights₂.Heights
