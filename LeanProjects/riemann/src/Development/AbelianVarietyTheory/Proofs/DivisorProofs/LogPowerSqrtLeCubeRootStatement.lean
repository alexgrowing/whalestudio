import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogPowerSqrtLeCubeRoot
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_power_sqrt_le_cube_root : ∀ (A B μ K : ℝ), 0 ≤ A → 0 ≤ B → 0 ≤ μ → 0 ≤ K → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
    A * (Real.log (1 / t) + B) ^ μ * t ^ ((1 : ℝ) / 2) + K * t ^ 2 ≤ t ^ ((1 : ℝ) / 3) := by
  first | exact @GlobalTheory.small_t_log_power_bound | exact GlobalTheory.small_t_log_power_bound | (intros; apply GlobalTheory.small_t_log_power_bound <;> assumption)
