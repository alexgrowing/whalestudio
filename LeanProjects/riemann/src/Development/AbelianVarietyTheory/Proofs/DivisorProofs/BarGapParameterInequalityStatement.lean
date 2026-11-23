import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BarGapParameterInequality
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bar_gap_parameter_inequality : ∀ (T D c0 h0 N f m k PP : ℝ), 4 * D + 4 ≤ T → 4 * T ^ 2 ≤ h0 → PP * T * N * f ^ 2 * m ^ 2 * k * D ≤ h0 →
    4 * (c0 + 2 * N + T + D + 1) ≤ h0 → 0 ≤ c0 → c0 ≤ 22 * f ^ 2 * N ^ 4 → D = f * (N * (N - 1) / 2) → 40 ≤ PP →
    N + 4 ≤ 2 * k → 2 ≤ m → 6 ≤ N → 8 ≤ f →
    (T + c0) * (T + D + 1) + c0 + 2 * N - 2 ≤ h0 ∧ 2 * N + D ≤ T := by
  first | exact @GlobalTheory.bar_gap_param_ineq | exact GlobalTheory.bar_gap_param_ineq | (intros; apply GlobalTheory.bar_gap_param_ineq <;> assumption)
