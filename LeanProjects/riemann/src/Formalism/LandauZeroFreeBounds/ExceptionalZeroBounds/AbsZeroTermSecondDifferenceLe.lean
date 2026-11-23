import Mathlib

noncomputable section

namespace Formalism.ZeroFreeDirichlet

private theorem one_add_rpow_le_one_add_mul {s p : ℝ} (hs : 0 ≤ s) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 + s) ^ p ≤ 1 + p * s := by
  have t := Real.geom_mean_le_arith_mean2_weighted hp0 (sub_nonneg.2 hp1)
    (by linarith : (0:ℝ) ≤ 1 + s) zero_le_one (by ring : p + (1 - p) = 1)
  rw [Real.one_rpow, mul_one] at t
  nlinarith [t]

private theorem le_one_add_mul_log_one_add {h : ℝ} (hh : 0 ≤ h) : h ≤ (1 + h) * Real.log (1 + h) := by
  have h1 : (0:ℝ) < 1 + h := by linarith
  have t := Real.log_le_sub_one_of_pos (inv_pos.2 h1)
  rw [Real.log_inv] at t
  have e : (1 + h) * (1 + h)⁻¹ = 1 := mul_inv_cancel₀ h1.ne'
  nlinarith [mul_le_mul_of_nonneg_left t h1.le]

lemma abs_zero_term_second_difference_le {y h β : ℝ} (hy : 1 ≤ y) (hh : 0 < h) (_hh1 : h ≤ 1) (hβ1 : 1 / 2 ≤ β)
    (hβ2 : β < 1) :
    |(y * (1 + h)) * (y ^ β / (β * (β - 1))) - y * ((y * (1 + h)) ^ β / (β * (β - 1)))
        + y * h * (y ^ β / β)| ≤ 2 * y ^ 2 * h ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have h1 : (0:ℝ) < 1 + h := by linarith
  have hβ0 : 0 < β := by linarith
  have hq : 0 < 1 - β := by linarith
  have hβne : β ≠ 0 := hβ0.ne'
  have hβ1ne : β - 1 ≠ 0 := by linarith
  have hq1ne : 1 - β ≠ 0 := hq.ne'
  have hmul : (y * (1 + h)) ^ β = y ^ β * (1 + h) ^ β := Real.mul_rpow hy0 h1.le
  have hAq : (1 + h) ^ β * (1 + h) ^ (1 - β) = 1 + h := by
    have e : β + (1 - β) = 1 := by ring
    rw [← Real.rpow_add h1, e, Real.rpow_one]
  have hBern : (1 + h) ^ (1 - β) ≤ 1 + (1 - β) * h :=
    one_add_rpow_le_one_add_mul hh.le hq.le (by linarith)
  have hD0 : (1 + h) ^ β ≤ 1 + β * h := one_add_rpow_le_one_add_mul hh.le hβ0.le hβ2.le
  have hA0 : 0 ≤ (1 + h) ^ β := Real.rpow_nonneg h1.le _
  have hB0 : 0 ≤ y ^ β := Real.rpow_nonneg hy0 _
  have hBy : y ^ β ≤ y := by
    have t := Real.rpow_le_rpow_of_exponent_le hy hβ2.le
    rwa [Real.rpow_one] at t
  set A := (1 + h) ^ β with hA
  set B := y ^ β with hB
  have hD1 : (1 + β * h - A) * (1 + (1 - β) * h) ≤ β * (1 - β) * h ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hBern hA0]
  have hD2 : 1 + β * h - A ≤ β * (1 - β) * h ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hD0) (mul_nonneg hq.le hh.le)]
  have key : (y * (1 + h)) * (B / (β * (β - 1))) - y * ((y * (1 + h)) ^ β / (β * (β - 1)))
      + y * h * (B / β) = -(y * B * ((1 + β * h - A) / (β * (1 - β)))) := by
    rw [hmul]
    field_simp
    ring
  rw [key, abs_neg]
  have hpos : 0 < β * (1 - β) := mul_pos hβ0 hq
  have hE0 : 0 ≤ (1 + β * h - A) / (β * (1 - β)) := div_nonneg (by linarith) hpos.le
  have hE : (1 + β * h - A) / (β * (1 - β)) ≤ h ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg hy0 hB0) hE0)]
  have s1 : y * B * ((1 + β * h - A) / (β * (1 - β))) ≤ y * B * h ^ 2 :=
    mul_le_mul_of_nonneg_left hE (mul_nonneg hy0 hB0)
  have s2 : y * B * h ^ 2 ≤ y * y * h ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBy hy0) (sq_nonneg h)
  nlinarith [mul_nonneg (sq_nonneg y) (sq_nonneg h)]

lemma abs_main_term_second_difference_le {y h γ : ℝ} (hy : 0 < y) (hh : 0 < h) :
    |y * ((y * (1 + h)) * Real.log (y * (1 + h)) - (1 + γ) * (y * (1 + h)))
      - (y * (1 + h)) * (y * Real.log y - (1 + γ) * y) - y * h * y| ≤ y ^ 2 * h ^ 2 := by
  have h1 : (0:ℝ) < 1 + h := by linarith
  have hlog : Real.log (y * (1 + h)) = Real.log y + Real.log (1 + h) :=
    Real.log_mul hy.ne' h1.ne'
  have key : y * ((y * (1 + h)) * Real.log (y * (1 + h)) - (1 + γ) * (y * (1 + h)))
      - (y * (1 + h)) * (y * Real.log y - (1 + γ) * y) - y * h * y
      = y ^ 2 * ((1 + h) * Real.log (1 + h) - h) := by
    rw [hlog]; ring
  rw [key]
  have hL1 : Real.log (1 + h) ≤ h := by
    have := Real.log_le_sub_one_of_pos h1
    linarith
  have hL2 := le_one_add_mul_log_one_add hh.le
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg y) (by linarith))]
  have t : (1 + h) * Real.log (1 + h) - h ≤ h ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hL1 h1.le]
  nlinarith [mul_le_mul_of_nonneg_left t (sq_nonneg y)]

lemma exp_neg_sqrt_log_le_sq {cs c₀ y z : ℝ} (hc0 : 0 ≤ c₀) (hcs : c₀ ≤ cs) (hy : 1 ≤ y) (hyz : y ≤ z) :
    Real.exp (-cs * Real.sqrt (Real.log z)) ≤ Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) ^ 2 := by
  have hlyz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyz
  have hs : Real.sqrt (Real.log y) ≤ Real.sqrt (Real.log z) := Real.sqrt_le_sqrt hlyz
  rw [sq, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_le_mul hcs hs (Real.sqrt_nonneg _) (le_trans hc0 hcs)]

end Formalism.ZeroFreeDirichlet
