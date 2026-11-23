import Mathlib

namespace Bl.general_b_fact_upper

theorem goal1 :
  ∀ {K : Type} [inst : NormedField.{0} K] [IsUltrametricDist.{0} K] {x y : K},
  LE.le.{0} (Norm.norm.{0} x) 1 →
    LE.le.{0} (Norm.norm.{0} y) 1 →
      ∀ (n : Nat),
        LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} x n) (HPow.hPow.{0, 0, 0} y n)))
          (Norm.norm.{0} (HSub.hSub.{0, 0, 0} x y)) := by
  intro K _ _ x y hx hy n
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1) - y ^ (n + 1) = x ^ n * (x - y) + (x ^ n - y ^ n) * y := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans ih

end Bl.general_b_fact_upper
