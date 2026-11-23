import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubharmonicLogConvexityQuotient
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EventuallyDifferentiableAtOfContDiffAtTwo
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subharmonic_log_convexity_quotient : ∀ (g : ℝ → ℝ) (δ c : ℝ), 0 < δ → ContDiffOn ℝ 2 g (Set.Ioo 0 δ) →
    (∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < δ → -c ≤ (GlobalTheory.leviForm (fun z : ℂ => g ‖z‖) w 1 1).re) →
    ∀ t t₁ : ℝ, 0 < t → t < t₁ → t₁ < δ →
      t * deriv g t + 2 * c * t ^ 2 ≤ (g t₁ + c * t₁ ^ 2 - (g t + c * t ^ 2)) / Real.log (t₁ / t) := by
  first | exact @GlobalTheory.slope_le_of_leviForm_radial_ge | exact GlobalTheory.slope_le_of_leviForm_radial_ge | (intros; apply GlobalTheory.slope_le_of_leviForm_radial_ge <;> assumption)
