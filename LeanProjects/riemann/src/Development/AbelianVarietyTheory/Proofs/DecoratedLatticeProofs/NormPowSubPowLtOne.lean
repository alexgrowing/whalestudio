import Mathlib

namespace GlobalTheory.UltrametricPowerDifference

theorem norm_pow_sub_pow_lt_one {K : Type} [NormedField K] [IsUltrametricDist K] (a b : K)
    (ha : ‖a‖ ≤ (1 : ℝ)) (hb : ‖b‖ ≤ (1 : ℝ)) (hab : ‖a - b‖ < (1 : ℝ)) (n : ℕ) :
    ‖a ^ n - b ^ n‖ < (1 : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [hsplit]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ha) ih
    · rw [norm_mul, norm_pow]
      exact lt_of_le_of_lt
        (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hb)) hab

end GlobalTheory.UltrametricPowerDifference
