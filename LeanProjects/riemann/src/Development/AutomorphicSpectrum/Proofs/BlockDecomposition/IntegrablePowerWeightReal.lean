import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanTateIntegral

open MeasureTheory

namespace GlobalTheory.CompanionTheory.RealTateConv

theorem abs_rpow_le_two_rpow_mul_one_add_abs_rpow (r : ℝ) {x : ℝ} (hx : 1 < |x|) :
    |x| ^ r ≤ (2 : ℝ) ^ |r| * (1 + |x|) ^ r := by
  have hx0 : 0 < |x| := by linarith
  have h1x : 0 < 1 + |x| := by linarith
  rcases le_or_gt 0 r with hr | hr
  · have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ |r| := Real.one_le_rpow (by norm_num) (abs_nonneg r)
    have h3 : |x| ^ r ≤ (1 + |x|) ^ r := Real.rpow_le_rpow hx0.le (by linarith) hr
    have h4 : 0 ≤ (1 + |x|) ^ r := Real.rpow_nonneg h1x.le r
    nlinarith
  · have h3 : (2 * |x|) ^ r ≤ (1 + |x|) ^ r :=
      Real.rpow_le_rpow_of_nonpos h1x (by linarith) hr.le
    rw [Real.mul_rpow (by norm_num) hx0.le] at h3
    have h5 : (2 : ℝ) ^ |r| * (2 : ℝ) ^ r = 1 := by
      rw [abs_of_neg hr, ← Real.rpow_add (by norm_num)]
      simp
    have h6 : (0 : ℝ) ≤ (2 : ℝ) ^ |r| := by positivity
    calc |x| ^ r = (2 : ℝ) ^ |r| * ((2 : ℝ) ^ r * |x| ^ r) := by
          rw [← mul_assoc, h5, one_mul]
      _ ≤ (2 : ℝ) ^ |r| * (1 + |x|) ^ r := mul_le_mul_of_nonneg_left h3 h6

theorem integrable_abs_rpow_mul_one_add_abs_rpow :
    ∀ (r N : ℝ), -1 < r → r + 1 < N →
      MeasureTheory.Integrable (fun x : ℝ => |x| ^ r * (1 + |x|) ^ (-N)) := by
  intro r N hr hN
  have hG : Integrable (fun x : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun x => |x| ^ r) x +
      (2 : ℝ) ^ |r| * (1 + ‖x‖) ^ (-(N - r))) :=
    ((integrableOn_abs_rpow hr).integrable_indicator measurableSet_Icc).add
      ((integrable_one_add_norm (by simp; linarith)).const_mul _)
  have hm : AEStronglyMeasurable (fun x : ℝ => |x| ^ r * (1 + |x|) ^ (-N)) volume :=
    ((measurable_abs.pow_const r).mul
      ((measurable_const.add measurable_abs).pow_const _)).aestronglyMeasurable
  refine hG.mono' hm (ae_of_all _ fun x => ?_)
  have h1x : 0 < 1 + |x| := by positivity
  have hA : 0 ≤ |x| ^ r := Real.rpow_nonneg (abs_nonneg x) r
  have hB : 0 ≤ (1 + |x|) ^ (-N) := Real.rpow_nonneg h1x.le _
  rw [Real.norm_of_nonneg (mul_nonneg hA hB)]
  have hC : 0 ≤ (2 : ℝ) ^ |r| * (1 + ‖x‖) ^ (-(N - r)) := by positivity
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx]
    have h1 : (1 + |x|) ^ (-N) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg x]) (by linarith)
    nlinarith
  · rw [Set.indicator_of_notMem hx, zero_add, Real.norm_eq_abs,
      show -(N - r) = r + -N by ring, Real.rpow_add h1x, ← mul_assoc]
    have hx1 : 1 < |x| := by
      by_contra h
      exact hx (abs_le.1 (not_lt.1 h))
    exact mul_le_mul_of_nonneg_right (abs_rpow_le_two_rpow_mul_one_add_abs_rpow r hx1) hB

end GlobalTheory.CompanionTheory.RealTateConv
