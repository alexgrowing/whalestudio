import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

theorem log_add_log_two_pi_le : log 280 + log (2 * π) ≤ 7.6 := by
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_gt_three
  rw [← Real.log_mul (by norm_num) (by positivity)]
  rw [Real.log_le_iff_le_exp (by positivity)]
  have hsplit : exp 7.6 = exp 1 ^ 7 * exp 0.6 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  rw [hsplit]
  have h7 : (2.7182818283 : ℝ) ^ 7 ≤ exp 1 ^ 7 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 7
  have h06 : (1 + 0.6 + 0.6 ^ 2 / 2 : ℝ) ≤ exp 0.6 :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have hpos : (0 : ℝ) ≤ (2.7182818283 : ℝ) ^ 7 := by positivity
  calc 280 * (2 * π) ≤ (2.7182818283 : ℝ) ^ 7 * (1 + 0.6 + 0.6 ^ 2 / 2) := by
        norm_num; nlinarith
    _ ≤ exp 1 ^ 7 * exp 0.6 :=
        mul_le_mul h7 h06 (by norm_num) (by positivity)

theorem log_two_pi_le : log (2 * π) ≤ 7.6 := by
  have h := log_add_log_two_pi_le
  have h280 : 0 ≤ log (280 : ℝ) := Real.log_nonneg (by norm_num)
  linarith

theorem half_log_add_le (D : ℝ) (hD : 1 ≤ D) :
    (1 / 2) * (log 280 + D * log (2 * π)) ≤ 3.8 * D := by
  have h1 := log_add_log_two_pi_le
  have h2 := log_two_pi_le
  nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ D - 1)]

theorem seven_point_six_le_log (ρ : ℝ) (hρ : 2 ^ 26 ≤ ρ) : 7.6 ≤ log ρ := by
  have h : log ((2 : ℝ) ^ 26) ≤ log ρ := Real.log_le_log (by positivity) hρ
  rw [Real.log_pow] at h
  have := Real.log_two_gt_d9
  push_cast at h
  linarith

theorem three_point_eight_le_half_log (D ρ : ℝ) (hD : 0 ≤ D) (hρ : 2 ^ 26 ≤ ρ) :
    3.8 * D ≤ (D / 2) * log ρ := by
  have h := seven_point_six_le_log ρ hρ
  nlinarith [mul_le_mul_of_nonneg_left h hD]

theorem half_log_add_le_half_log (D ρ : ℝ) (hD : 1 ≤ D) (hρ : 2 ^ 26 ≤ ρ) :
    (1 / 2) * (log 280 + D * log (2 * π)) ≤ 3.8 * D ∧ 3.8 * D ≤ (D / 2) * log ρ :=
  ⟨half_log_add_le D hD, three_point_eight_le_half_log D ρ (by linarith) hρ⟩

def vanishingOrderBound (T D N : ℝ) : ℝ := T + 2 * D + 4 + N

end GroundTheory.Heights₂.Heights
