import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothBoundedGradientOnHalfBall
import Mathlib
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_bounded_gradient_on_half_ball : ∀ {e : ℕ} (f : (Fin e → ℂ) → ℝ), ContDiffOn ℝ ∞ f (Metric.ball (0 : Fin e → ℂ) 1) → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.closedBall (0 : Fin e → ℂ) (1 / 2), |f z| ≤ C ∧ ∀ w : Fin e → ℂ, (fderiv ℝ f z w) ^ 2 + (fderiv ℝ f z (Complex.I • w)) ^ 2 ≤ C * ∑ k, ‖w k‖ ^ 2 := by
  first | exact @GlobalTheory.smooth_polydisc_value_fderiv_bound | exact GlobalTheory.smooth_polydisc_value_fderiv_bound | (intros; apply GlobalTheory.smooth_polydisc_value_fderiv_bound <;> assumption)
