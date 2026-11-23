import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

noncomputable def logCutoff (k : ℕ) (z : ℂ) : ℝ :=
  if z = 0 then 0 else Real.smoothTransition (2 + Real.log ‖z‖ / ((k : ℝ) + 1))

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma logCutoff_eq_zero_of_norm_le (k : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ Real.exp (-2 * ((k : ℝ) + 1))) : _root_.GlobalTheory.GoodTop.logCutoff k z = 0 := by
  unfold _root_.GlobalTheory.GoodTop.logCutoff
  split_ifs with h0
  · rfl
  apply Real.smoothTransition.zero_of_nonpos
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlog : Real.log ‖z‖ ≤ -2 * ((k : ℝ) + 1) := by
    rw [← Real.log_exp (-2 * ((k : ℝ) + 1))]
    exact Real.log_le_log (norm_pos_iff.mpr h0) hz
  rw [← sub_nonneg, show 0 - (2 + Real.log ‖z‖ / ((k : ℝ) + 1)) =
    (-2 * ((k : ℝ) + 1) - Real.log ‖z‖) / ((k : ℝ) + 1) by field_simp; ring]
  exact div_nonneg (by linarith) hk.le

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
lemma _root_.GlobalTheory.GoodTop.contDiff_logCutoff (k : ℕ) : ContDiff ℝ ∞ (_root_.GlobalTheory.GoodTop.logCutoff k) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases h0 : z = 0
  · subst h0
    have hev : _root_.GlobalTheory.GoodTop.logCutoff k =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (Real.exp_pos (-2 * ((k : ℝ) + 1)))] with w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      exact logCutoff_eq_zero_of_norm_le k hw.le
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hev : _root_.GlobalTheory.GoodTop.logCutoff k =ᶠ[𝓝 z]
        fun w => Real.smoothTransition (2 + Real.log ‖w‖ / ((k : ℝ) + 1)) := by
      filter_upwards [isOpen_ne.mem_nhds h0] with w hw
      simp only [_root_.GlobalTheory.GoodTop.logCutoff, if_neg (show w ≠ 0 from hw)]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    refine Real.smoothTransition.contDiff.contDiffAt.comp z ?_
    refine contDiffAt_const.add (ContDiffAt.div_const ?_ _)
    exact (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr h0)).comp z (contDiffAt_norm ℝ h0)

end GlobalTheory.GoodTop
