import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.ThetaDerivNe

noncomputable section

open Complex

namespace PI.SSE

def qe (τ : ℂ) (n : ℕ) : ℂ := cexp (Real.pi * I * τ * ((n : ℂ) * ((n : ℂ) + 1)))

lemma term_pos (τ : ℂ) (n : ℕ) :
    jacobiTheta₂'_term (n : ℤ) (1 / 2 + τ / 2) τ
      = 2 * Real.pi * I * (n : ℂ) * ((-1) ^ n * qe τ n) := by
  have hexp : cexp (2 * Real.pi * I * (n : ℂ) * (1 / 2 + τ / 2) + Real.pi * I * (n : ℂ) ^ 2 * τ) =
      (-1) ^ n * qe τ n := by
    rw [qe, show 2 * (Real.pi : ℂ) * I * (n : ℂ) * (1 / 2 + τ / 2) + Real.pi * I * (n : ℂ) ^ 2 * τ =
        (n : ℂ) * (Real.pi * I) + Real.pi * I * τ * ((n : ℂ) * ((n : ℂ) + 1)) by ring,
      Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  simp only [jacobiTheta₂'_term, jacobiTheta₂_term, Int.cast_natCast, hexp]

lemma term_neg (τ : ℂ) (n : ℕ) :
    jacobiTheta₂'_term (-((n : ℤ) + 1)) (1 / 2 + τ / 2) τ
      = 2 * Real.pi * I * ((n : ℂ) + 1) * ((-1) ^ n * qe τ n) := by
  have hm : cexp (-(Real.pi * I)) = -1 := by
    rw [Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have hexp : cexp (2 * Real.pi * I * (-((n : ℂ) + 1)) * (1 / 2 + τ / 2) +
      Real.pi * I * (-((n : ℂ) + 1)) ^ 2 * τ) = (-1) ^ (n + 1) * qe τ n := by
    rw [qe, show 2 * (Real.pi : ℂ) * I * (-((n : ℂ) + 1)) * (1 / 2 + τ / 2) +
        Real.pi * I * (-((n : ℂ) + 1)) ^ 2 * τ =
        ((n + 1 : ℕ) : ℂ) * (-(Real.pi * I)) + Real.pi * I * τ * ((n : ℂ) * ((n : ℂ) + 1)) by push_cast; ring,
      Complex.exp_add, Complex.exp_nat_mul, hm]
  simp only [jacobiTheta₂'_term, jacobiTheta₂_term, Int.cast_neg, Int.cast_add, Int.cast_natCast,
    Int.cast_one, hexp]
  ring

lemma hasSum_series (τ : ℂ) (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => 2 * Real.pi * I * ((2 * (n : ℂ) + 1) * ((-1) ^ n * qe τ n)))
      (jacobiTheta₂' (1 / 2 + τ / 2) τ) := by
  have h := (hasSum_jacobiTheta₂'_term (1 / 2 + τ / 2) hτ).nat_add_neg_add_one
  convert h using 1
  funext n
  rw [term_pos, term_neg]
  ring

lemma norm_qe (τ : ℂ) (n : ℕ) :
    ‖qe τ n‖ = Real.exp (-(Real.pi * τ.im * ((n : ℝ) * ((n : ℝ) + 1)))) := by
  rw [qe, Complex.norm_exp]
  congr 1
  have e : (Real.pi : ℂ) * I * τ * ((n : ℂ) * ((n : ℂ) + 1)) =
      ((Real.pi * ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) * (I * τ) := by
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

lemma norm_succ_le (τ : ℂ) (hy : 0 < τ.im) (n : ℕ) :
    ‖(2 * ((n + 1 : ℕ) : ℂ) + 1) * ((-1) ^ (n + 1) * qe τ (n + 1))‖
      ≤ (3 * Real.exp (-(2 * Real.pi * τ.im))) ^ (n + 1) := by
  have hc : ‖(2 * ((n + 1 : ℕ) : ℂ) + 1)‖ = ((2 * (n + 1) + 1 : ℕ) : ℝ) := by
    rw [show (2 * ((n + 1 : ℕ) : ℂ) + 1) = ((2 * (n + 1) + 1 : ℕ) : ℂ) by push_cast; ring]
    exact Complex.norm_natCast _
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_qe, hc]
  have hA : ((2 * (n + 1) + 1 : ℕ) : ℝ) ≤ 3 ^ (n + 1) := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 2 by norm_num) (n + 1)
    push_cast at h ⊢
    norm_num at h
    linarith
  have hB : Real.exp (-(Real.pi * τ.im * (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)))) ≤
      Real.exp (-(2 * Real.pi * τ.im)) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hy.le)
      (mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1))]
  calc ((2 * (n + 1) + 1 : ℕ) : ℝ) * Real.exp (-(Real.pi * τ.im * (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))))
      ≤ 3 ^ (n + 1) * Real.exp (-(2 * Real.pi * τ.im)) ^ (n + 1) :=
        mul_le_mul hA hB (Real.exp_pos _).le (by positivity)
    _ = (3 * Real.exp (-(2 * Real.pi * τ.im))) ^ (n + 1) := (mul_pow _ _ _).symm

lemma small_of_im (y : ℝ) (hy : 0 < y) (h3 : 3 ≤ 4 * y ^ 2) :
    3 * Real.exp (-(2 * Real.pi * y)) < 1 / 2 := by
  have hy2 : 1 / 2 < y := by nlinarith
  have hx : 3 < 2 * Real.pi * y := by nlinarith [Real.pi_gt_three]
  have he : 6 < Real.exp (2 * Real.pi * y) := by
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * Real.pi * y by positivity)
    nlinarith
  have hp := Real.exp_pos (2 * Real.pi * y)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ hp]
  linarith

theorem thetaDerivNe : ThetaDerivNe := by
  intro τ hy h3 h0
  have hS := hasSum_series τ hy
  rw [h0] at hS
  let a : ℕ → ℂ := fun n => (2 * (n : ℂ) + 1) * ((-1) ^ n * qe τ n)
  have hc : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hS2 : HasSum a 0 := by
    have h := hS.div_const (2 * Real.pi * I)
    rw [zero_div] at h
    simpa [a, mul_div_cancel_left₀ _ hc] using h
  have a0 : a 0 = 1 := by simp [a, qe]
  have hT := (hasSum_nat_add_iff' 1).mpr hS2
  rw [Finset.sum_range_one, a0, zero_sub] at hT
  set r := 3 * Real.exp (-(2 * Real.pi * τ.im)) with hrdef
  have hr : r < 1 / 2 := small_of_im τ.im hy h3
  have hr0 : 0 ≤ r := by positivity
  have hg : HasSum (fun n : ℕ => r ^ (n + 1)) (r * (1 - r)⁻¹) := by
    have h := (hasSum_geometric_of_lt_one hr0 (by linarith)).mul_left r
    simpa only [pow_succ'] using h
  have hb := tsum_of_norm_bounded (f := fun n => a (n + 1)) hg (fun n => norm_succ_le τ hy n)
  rw [hT.tsum_eq, norm_neg, norm_one] at hb
  have hlt : r * (1 - r)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one (by linarith)]
    linarith
  linarith

end PI.SSE

end
