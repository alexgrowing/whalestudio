import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductIntegralFinite
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_integral_finite : ∀ {e : ℕ} (r : ℝ) (f : Fin e → ℂ → ENNReal), (∀ k, Measurable (f k)) → (∀ k, ∫⁻ u in Metric.ball (0 : ℂ) r, f k u < ⊤) → ∫⁻ z in Metric.ball (0 : Fin e → ℂ) r, ∏ k, f k (z k) < ⊤ := by
  first | exact @GlobalTheory.setLIntegral_ball_pi_prod_lt_top' | exact GlobalTheory.setLIntegral_ball_pi_prod_lt_top' | (intros; apply GlobalTheory.setLIntegral_ball_pi_prod_lt_top' <;> assumption)
