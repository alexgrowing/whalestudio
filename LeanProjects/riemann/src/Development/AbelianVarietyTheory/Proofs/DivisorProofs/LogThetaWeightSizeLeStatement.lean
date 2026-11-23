import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogThetaWeightSizeLe
open Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_le_twenty_mul_of_bounds : ∀ (f r Lb S sz : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ Lb → Real.log (f * r) ≤ Lb → (∃ N : ℕ, S = N) → Real.log S ≤ 10 * Lb → 0 ≤ sz → sz ≤ (1 + r) * S + r * f * (4 * (f * r + 1) + 1) → Real.log sz ≤ 20 * Lb := by
  first | exact @GlobalTheory.log_theta_weight_size_le | exact GlobalTheory.log_theta_weight_size_le | (intros; apply GlobalTheory.log_theta_weight_size_le <;> assumption)
