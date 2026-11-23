import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem alternatingWord_numerical_bounds :
    ∀ (l : ℕ) (B η S M b : ℝ), 11 ≤ l → 100 ≤ B → 0 ≤ η → 0 ≤ S → 2 * η + S ≤ B / 10 →
      |M - B| ≤ η → |b - B| ≤ η → (M + S) / 2 ≤ b ∧
      2 * ((M + S + η) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + (Real.logb l (2 * (M + S + η)) + 1))
        + η + 1 ≤ b := by
  intro l B η S M b hl hB hη hS hBS hM hb
  have hl' : (11:ℝ) ≤ l := by exact_mod_cast hl
  rw [abs_le] at hM hb
  obtain ⟨hM1, hM2⟩ := hM
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨by linarith, ?_⟩
  have hx1 : M + S + η ≤ 11/10 * B := by linarith
  have hx0 : 100 ≤ M + S + η := by linarith
  have hfrac : (2 * (l:ℝ) - 1) / ((l:ℝ) - 1) ^ 2 ≤ 21/100 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have hfrac0 : 0 ≤ (2 * (l:ℝ) - 1) / ((l:ℝ) - 1) ^ 2 :=
    div_nonneg (by linarith) (sq_nonneg _)
  have h1 : (M + S + η) * (2 * (l:ℝ) - 1) / ((l:ℝ) - 1) ^ 2 ≤ 231/1000 * B := by
    rw [mul_div_assoc]
    nlinarith [mul_le_mul_of_nonneg_left hfrac (show 0 ≤ M + S + η by linarith),
      mul_le_mul_of_nonneg_right hx1 hfrac0]
  have hlogl : 1 ≤ Real.log l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlog100 : Real.log 100 < 5 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    have he : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc (100:ℝ) < 2.7182818283 ^ 5 := by norm_num
      _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h.le 5
  have hlogy : Real.log (2 * (M + S + η)) ≤ 2 * (M + S + η) / 100 - 1 + Real.log 100 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 * (M + S + η) / 100 by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at this
    linarith
  have hlogb : Real.logb l (2 * (M + S + η)) ≤ 2 * (M + S + η) / 100 + 4 := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    have : 0 ≤ Real.log (2 * (M + S + η)) := Real.log_nonneg (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hlogl (show 0 ≤ 2 * (M + S + η) / 100 + 4 by linarith)]
  linarith

end GlobalTheory
