import Mathlib
open Real

namespace GlobalTheory

theorem log_size_bounds_class_number_volume : ∀ f r L lrd lM lh w d D : ℝ, 1 ≤ f → 2 ≤ r → 1 ≤ L → log f + log r ≤ L → 0 ≤ lrd → lrd ≤ 2*L → 0 ≤ lM → lM ≤ 30*L → lh ≤ f*lrd + 2*f*log (1 + f*lrd) → 1 ≤ d → log d / 2 ≤ lrd → 0 < w → D = f*r*(r-1)/2 → lh ≤ 9*f*L ∧ lh + 2*f*lM ≤ 69*f*L ∧ log 2 + lh + 2*f*(r^2+1)*lM + f*(r^2-1)/2*lrd ≤ 80*f*r^2*L ∧ log 2 + lh + 2*f*(r^2+1)*lM + f*(r^2-1)/2*lrd + f*r^2/2*log r ≤ 81*f*r^2*L ∧ 2 + D*log (1600*r^2/π) + (2*f*r)^2*log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) + (log 2 + lh + 2*f*(r^2+1)*lM + f*(r^2-1)/2*lrd) ≤ 242*(f*r*L)^2 + 4*f^2*r^2*log (max 1 w) ∧ (w ≤ 3*exp (2*L) → 2 + D*log (1600*r^2/π) + (2*f*r)^2*log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) + (log 2 + lh + 2*f*(r^2+1)*lM + f*(r^2-1)/2*lrd) ≤ 250*f^2*r^2*L) := by
  intro f r L lrd lM lh w d D hf hr hL hfr hrd0 hrd hM0 hM hlh hd hdl hw hD
  have f0 : 0 < f := by linarith
  have r0 : 0 < r := by linarith
  have L0 : 0 < L := by linarith
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have lf0 : 0 ≤ log f := log_nonneg hf
  have lr2 : log 2 ≤ log r := log_le_log (by norm_num) hr
  have lLL : log L ≤ L - 1 := log_le_sub_one_of_pos L0
  have hfL : 1 ≤ f * L := by nlinarith
  have l4 : log 4 = 2 * log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, log_pow]; norm_num
  have l8 : log 8 = 3 * log 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num, log_pow]; norm_num
  have l16 : log 16 = 4 * log 2 := by
    rw [show (16:ℝ) = 2^4 by norm_num, log_pow]; norm_num
  have l1024 : log 1024 = 10 * log 2 := by
    rw [show (1024:ℝ) = 2^10 by norm_num, log_pow]; norm_num
  have l5 : log 5 ≤ 3 * log 2 := l8 ▸ log_le_log (by norm_num) (by norm_num)
  have l15 : log 5 + log 3 ≤ 4 * log 2 := by
    rw [← log_mul (by norm_num) (by norm_num), ← l16]
    exact log_le_log (by norm_num) (by norm_num)
  have hfrd : f * lrd ≤ f * (2 * L) := mul_le_mul_of_nonneg_left hrd f0.le
  have hfrd0 : 0 ≤ f * lrd := by positivity
  have h1 : log (1 + f * lrd) ≤ 2 * L := by
    have : log (1 + f * lrd) ≤ log (4 * f * L) := log_le_log (by linarith) (by linarith)
    rw [log_mul (by positivity) L0.ne', log_mul (by norm_num) f0.ne'] at this
    linarith
  have c1 : lh ≤ 9 * f * L := by
    have := mul_le_mul_of_nonneg_left h1 f0.le
    linarith
  have hfM : f * lM ≤ f * (30 * L) := mul_le_mul_of_nonneg_left hM f0.le
  have r2 : 4 ≤ r ^ 2 := by nlinarith
  have c3 : log 2 + lh + 2*f*(r^2+1)*lM + f*(r^2-1)/2*lrd ≤ 80*f*r^2*L := by
    have a := mul_le_mul_of_nonneg_left hfM (show 0 ≤ r^2+1 by positivity)
    have b := mul_le_mul_of_nonneg_left hfrd (show 0 ≤ r^2-1 by linarith)
    have c := mul_le_mul_of_nonneg_left r2 (show 0 ≤ f * L by linarith)
    linarith
  have lrL : log r ≤ L := by linarith
  have hfr2 : 0 ≤ f * r ^ 2 := by positivity
  have c4 : f*r^2/2*log r ≤ f*r^2*L := by
    have := mul_le_mul_of_nonneg_left lrL hfr2
    have : 0 ≤ f * r^2 * L := by positivity
    linarith
  have pi3 := Real.pi_gt_three
  have h2 : log (1600*r^2/π) ≤ 10 * log 2 + 2 * L := by
    have : log (1600*r^2/π) ≤ log (1024 * r^2) := by
      apply log_le_log (by positivity)
      rw [div_le_iff₀ pi_pos]
      nlinarith
    rw [log_mul (by norm_num) (by positivity), log_pow, l1024] at this
    push_cast at this
    linarith
  have hD0 : 0 ≤ D := by
    rw [hD]; have : 0 ≤ r - 1 := by linarith
    positivity
  have hD1 : D ≤ f * r ^ 2 / 2 := by
    rw [hD]; have : 0 ≤ f * r := by positivity
    nlinarith
  have h3 : D * log (1600*r^2/π) ≤ f * r^2 / 2 * (9 * L) := by
    calc D * log (1600*r^2/π) ≤ D * (9 * L) := mul_le_mul_of_nonneg_left (by linarith) hD0
      _ ≤ _ := mul_le_mul_of_nonneg_right hD1 (by positivity)
  have m1 : (1:ℝ) ≤ max 1 w := le_max_left _ _
  have sd : 1 ≤ √d := Real.one_le_sqrt.mpr hd
  have eM : 1 ≤ exp lM := one_le_exp hM0
  have h4 : max 1 (exp lM*f*w*√d) ≤ exp lM*f*max 1 w*√d := by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le eM hf) m1) sd
    · gcongr; exact le_max_right _ _
  have h5 : log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d))
      ≤ log 5 - log 2 + 37 * L + log (max 1 w) := by
    have : log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d))
        ≤ log (5*f*r*exp (3/2*lrd)*(exp lM*f*max 1 w*√d)) := by
      apply log_le_log (by positivity)
      gcongr
    have e : log (5*f*r*exp (3/2*lrd)*(exp lM*f*max 1 w*√d))
        = log 5 + log f + log r + 3/2*lrd + (lM + log f + log (max 1 w) + log d / 2) := by
      rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity), log_exp, log_exp,
        log_sqrt (by linarith)]
    linarith
  have hX : 0 ≤ f^2 * r^2 := by positivity
  have hA : f * r^2 * L ≤ f^2 * r^2 * L := by
    have : 0 ≤ f * r^2 * L := by positivity
    have := mul_le_mul_of_nonneg_left hf this
    linarith
  have hB : 4 ≤ f * r^2 * L := by
    have := mul_le_mul_of_nonneg_left hfL (show 0 ≤ r^2 by positivity)
    linarith
  have hC : f^2 * r^2 * L ≤ (f*r*L)^2 := by
    have : 0 ≤ f^2 * r^2 * L := by positivity
    have := mul_le_mul_of_nonneg_left hL this
    linarith
  refine ⟨c1, by linarith, c3, by linarith, ?_, fun hw3 => ?_⟩
  · have h6 : log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) ≤ 39 * L + log (max 1 w) := by
      linarith
    have := mul_le_mul_of_nonneg_left h6 hX
    generalize log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) = Y at this ⊢
    linarith
  · have h7 : log (max 1 w) ≤ log 3 + 2 * L := by
      have e : 1 ≤ exp (2 * L) := one_le_exp (by linarith)
      have : log (max 1 w) ≤ log (3 * exp (2 * L)) :=
        log_le_log (by positivity) (max_le (by linarith) hw3)
      rwa [log_mul (by norm_num) (by positivity), log_exp] at this
    have h6 : log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) ≤ 411/10 * L := by
      linarith
    have := mul_le_mul_of_nonneg_left h6 hX
    generalize log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) = Y at this ⊢
    linarith

end GlobalTheory
