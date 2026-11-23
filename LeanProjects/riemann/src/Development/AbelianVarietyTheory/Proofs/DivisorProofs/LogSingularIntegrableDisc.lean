import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff

namespace GlobalTheory.PoincareDisc

open Real Set Filter Topology
open scoped ENNReal

theorem integrableOn_radial {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    IntegrableOn (fun s : ℝ => 1 / (s * Real.log s ^ 2)) (Ioc 0 r) := by
  have hcont : ContinuousOn (fun s : ℝ => -(Real.log s)⁻¹) (Icc 0 r) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      apply ContinuousAt.continuousWithinAt
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
      simp only [Real.log_zero, inv_zero, neg_zero]
      simpa using (Real.tendsto_log_nhdsNE_zero.inv_tendsto_atBot).neg
    · apply ContinuousAt.continuousWithinAt
      have hne : Real.log x ≠ 0 := by
        have := Real.log_neg h (lt_of_le_of_lt hx.2 hr1)
        exact this.ne
      exact ((Real.continuousAt_log h.ne').inv₀ hne).neg
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) r, HasDerivAt (fun s : ℝ => -(Real.log s)⁻¹)
      (1 / (x * Real.log x ^ 2)) x := by
    intro x hx
    have hne : Real.log x ≠ 0 := (Real.log_neg hx.1 (hx.2.trans hr1)).ne
    have h := ((Real.hasDerivAt_log hx.1.ne').inv hne).neg
    refine h.congr_deriv ?_
    field_simp
  have hpos : ∀ x ∈ Ioo (0 : ℝ) r, 0 ≤ 1 / (x * Real.log x ^ 2) := by
    intro x hx
    have := hx.1
    positivity
  exact intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv hpos

theorem lintegral_ball_lt_top (r : ℝ) (hr : r ≤ 1 / 2) :
    ∫⁻ u in Metric.ball (0 : ℂ) r, ENNReal.ofReal (1 / (‖u‖ ^ 2 * tOf u ^ 2)) < ⊤ := by
  rcases le_or_gt r 0 with hr0 | hr0
  · rw [Metric.ball_eq_empty.2 hr0]
    simp
  have hr1 : r < 1 := by linarith
  set G : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (4 * π ^ 2 * (1 / (s * Real.log s ^ 2)))
    with hG
  rw [← lintegral_indicator Metric.isOpen_ball.measurableSet,
    ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have h1 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 •
      (Metric.ball (0 : ℂ) r).indicator
        (fun u => ENNReal.ofReal (1 / (‖u‖ ^ 2 * tOf u ^ 2))) (Complex.polarCoord.symm p) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        (Iio r).indicator G p.1 * (fun _ : ℝ => (1 : ℝ≥0∞)) p.2 := by
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
    have hp1 : 0 < p.1 := hp.1
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    by_cases hpr : p.1 < r
    · have hmem : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) r := by
        rw [Metric.mem_ball, dist_zero_right, hn]; exact hpr
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show p.1 ∈ Iio r from hpr),
        smul_eq_mul, mul_one, ← ENNReal.ofReal_mul hp1.le, hG]
      congr 1
      rw [tOf, hn]
      have hl : Real.log p.1 ≠ 0 := (Real.log_neg hp1 (hpr.trans hr1)).ne
      field_simp
      ring
    · have hmem : Complex.polarCoord.symm p ∉ Metric.ball (0 : ℂ) r := by
        rw [Metric.mem_ball, dist_zero_right, hn]; exact hpr
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show p.1 ∉ Iio r from hpr)]
      simp
  have hGm : Measurable G := by
    simp only [hG]
    fun_prop
  rw [h1, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := (Iio r).indicator G) (g := fun _ : ℝ => (1 : ℝ≥0∞))
      (hGm.indicator measurableSet_Iio).aemeasurable (by fun_prop)]
  refine ENNReal.mul_lt_top ?_ ?_
  · rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
    have hsub : Iio r ∩ Ioi (0 : ℝ) ⊆ Ioc 0 r := fun x hx => ⟨hx.2, hx.1.le⟩
    refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
    have hint : IntegrableOn (fun s : ℝ => 4 * π ^ 2 * (1 / (s * Real.log s ^ 2))) (Ioc 0 r) :=
      (integrableOn_radial hr0 hr1).const_mul _
    exact hint.lintegral_lt_top
  · simp

end GlobalTheory.PoincareDisc
