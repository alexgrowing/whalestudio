import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartIbpSteps
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartCutoffParts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyIntegrable
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PHermFormCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyDifferenceBound

theorem cross_le {u U χ a p G : ℝ} (hU : |u| ≤ U) (hχ : 0 ≤ χ) (hp : 0 ≤ p) (hG : 0 ≤ G)
    (ha : |a| ≤ Real.sqrt p * Real.sqrt G) :
    -(u * (χ * a + χ * a)) ≤ 2 * U ^ 2 * p + χ * χ * G / 2 := by
  have hsp := Real.sq_sqrt hp
  have hsG := Real.sq_sqrt hG
  have h0 : 0 ≤ |u| := abs_nonneg u
  have hua : -(u * a) ≤ |u| * |a| := by
    rw [← abs_mul]
    exact neg_le_abs _
  have h1 : -(u * (χ * a + χ * a)) ≤ 2 * χ * (|u| * |a|) := by
    nlinarith [mul_le_mul_of_nonneg_left hua hχ]
  have hb : |u| * |a| ≤ U * (Real.sqrt p * Real.sqrt G) := mul_le_mul hU ha (abs_nonneg a) (h0.trans hU)
  have h2 : 2 * χ * (|u| * |a|) ≤ 2 * χ * (U * (Real.sqrt p * Real.sqrt G)) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have h3 : 2 * χ * (U * (Real.sqrt p * Real.sqrt G)) ≤ 2 * U ^ 2 * p + χ * χ * G / 2 := by
    nlinarith [sq_nonneg (2 * U * Real.sqrt p - χ * Real.sqrt G)]
  linarith

end ChartEnergyDifferenceBound

open ChartIntegrationByPartsSymmetry ChartEnergyDifferenceBound

theorem ChartDiffEnergy.proof (hE : ChartCutoffEnergy.Statement) : ChartDiffEnergy.Statement := by
  intro n A B T hA hB hT
  set φ : Fin n → (Fin (n + 1) → ℂ) → ℝ := fun i => hermChartPot (T i) with hφdef
  set u : (Fin (n + 1) → ℂ) → ℝ := fun y => hermChartPot A y - hermChartPot B y with hudef
  have hφ3 : ∀ i, ContDiff ℝ 3 (φ i) := fun i => contDiff_hermChartPot_of_le 3 (hT i)
  have hφ2 : ∀ i, ContDiff ℝ 2 (φ i) := fun i => contDiff_hermChartPot_of_le 2 (hT i)
  have hu3 : ContDiff ℝ 3 u := (contDiff_hermChartPot_of_le 3 hA).sub (contDiff_hermChartPot_of_le 3 hB)
  have hu1 : ContDiff ℝ 1 u := hu3.of_le (by norm_num)
  have hGc : Continuous (gradDens φ u u) := continuous_gradDens hφ2 hu1 hu1
  have hG0 : ∀ y, 0 ≤ gradDens φ u u y := gradDens_chart_nonneg hT u
  obtain ⟨U, hU⟩ := ChartEnergyIntegrableAlt.pot_sub_bound HermFormCompare.proof hA hB
  have hUa : ∀ y, |u y| ≤ U := fun y => by
    have := hU y
    rwa [Real.norm_eq_abs] at this
  obtain ⟨K, hK⟩ := hE n T hT
  have hI : Integrable (fun y => u y * maDens (Fin.cons u φ) y) :=
    integrable_pot_mul_maDensity hA hB hA hB hT
  set I : ℝ := ∫ y, |u y * maDens (Fin.cons u φ) y| with hIdef
  have hψG : ∀ k : ℕ, Integrable (fun y => chartCutoff k y * chartCutoff k y * gradDens φ u u y) := fun k =>
    (((contDiff_chartCutoff k 0).continuous.mul (contDiff_chartCutoff k 0).continuous).mul
      hGc).integrable_of_hasCompactSupport (hasCompactSupport_chartCutoff k).mul_right.mul_right
  have hX : ∀ k : ℕ, ∫ y, chartCutoff k y * chartCutoff k y * gradDens φ u u y ≤ 2 * I + 4 * U ^ 2 * K := by
    intro k
    set χ : (Fin (n + 1) → ℂ) → ℝ := chartCutoff k with hχdef
    have hχ3 : ContDiff ℝ 3 χ := contDiff_chartCutoff k 3
    have hχ1 : ContDiff ℝ 1 χ := contDiff_chartCutoff k 1
    have hψ3 : ContDiff ℝ 3 (fun y => χ y * χ y) := hχ3.mul hχ3
    have hψc : HasCompactSupport (fun y => χ y * χ y) := (hasCompactSupport_chartCutoff k).mul_right
    obtain ⟨i1, i2, i3, heq⟩ := parts_cutoff hφ3 hψ3 hψc hu3 hu3
    have hP : Integrable (gradDens φ χ χ) :=
      (continuous_gradDens hφ2 hχ1 hχ1).integrable_of_hasCompactSupport
        (hasCompactSupport_gradDens_left φ χ (hasCompactSupport_chartCutoff k))
    have hL : ∀ y, gradDens φ (fun y => χ y * χ y) u y = χ y * gradDens φ χ u y + χ y * gradDens φ χ u y :=
      fun y => (gradDensLeibniz_thm n φ χ χ u y (hχ1.differentiable one_ne_zero y)
        (hχ1.differentiable one_ne_zero y)).1
    have hpt : ∀ y, -(χ y * χ y * u y * maDens (Fin.cons u φ) y) - u y * gradDens φ (fun y => χ y * χ y) u y ≤
        |u y * maDens (Fin.cons u φ) y| + (2 * U ^ 2 * gradDens φ χ χ y + χ y * χ y * gradDens φ u u y / 2) := by
      intro y
      rw [hL y]
      have h0 : 0 ≤ χ y := chartCutoff_nonneg k y
      have h1 : χ y ≤ 1 := chartCutoff_le_one k y
      have hψ0 : 0 ≤ χ y * χ y := mul_nonneg h0 h0
      have hψ1 : χ y * χ y ≤ 1 := by nlinarith
      have ht := neg_abs_le (u y * maDens (Fin.cons u φ) y)
      have ht0 := abs_nonneg (u y * maDens (Fin.cons u φ) y)
      have ha : -(χ y * χ y * u y * maDens (Fin.cons u φ) y) ≤ |u y * maDens (Fin.cons u φ) y| := by
        nlinarith [mul_nonneg hψ0 (by linarith : 0 ≤ |u y * maDens (Fin.cons u φ) y| + u y * maDens (Fin.cons u φ) y),
          mul_nonneg (by linarith : 0 ≤ 1 - χ y * χ y) ht0]
      have hb := cross_le (hUa y) h0 (gradDens_chart_nonneg hT χ y) (hG0 y) (abs_gradDens_chart_le hT χ u y)
      linarith
    have i1n : Integrable (fun y => -(χ y * χ y * u y * maDens (Fin.cons u φ) y)) := i1.neg
    have iL : Integrable (fun y => -(χ y * χ y * u y * maDens (Fin.cons u φ) y) -
        u y * gradDens φ (fun y => χ y * χ y) u y) := i1n.sub i3
    have iA : Integrable (fun y => |u y * maDens (Fin.cons u φ) y|) := hI.abs
    have iP : Integrable (fun y => 2 * U ^ 2 * gradDens φ χ χ y) := hP.const_mul _
    have iG : Integrable (fun y => χ y * χ y * gradDens φ u u y / 2) := i2.div_const 2
    have iPG : Integrable (fun y => 2 * U ^ 2 * gradDens φ χ χ y + χ y * χ y * gradDens φ u u y / 2) := iP.add iG
    have iR : Integrable (fun y => |u y * maDens (Fin.cons u φ) y| +
        (2 * U ^ 2 * gradDens φ χ χ y + χ y * χ y * gradDens φ u u y / 2)) := iA.add iPG
    have hXeq : ∫ y, χ y * χ y * gradDens φ u u y =
        ∫ y, (-(χ y * χ y * u y * maDens (Fin.cons u φ) y) - u y * gradDens φ (fun y => χ y * χ y) u y) := by
      rw [integral_sub i1n i3, integral_neg]
      linarith
    have hmono := integral_mono iL iR hpt
    rw [← hXeq, integral_add iA iPG, integral_add iP iG, integral_const_mul, integral_div] at hmono
    have hKk : 2 * U ^ 2 * ∫ y, gradDens φ χ χ y ≤ 2 * U ^ 2 * K :=
      mul_le_mul_of_nonneg_left (hK k) (by positivity)
    linarith
  set f : ℕ → (Fin (n + 1) → ℂ) → ENNReal :=
    fun k y => ENNReal.ofReal (chartCutoff k y * chartCutoff k y * gradDens φ u u y) with hfdef
  have hmono : ∀ y, Monotone fun k => f k y := by
    intro y a b hab
    apply ENNReal.ofReal_le_ofReal
    have h1 := chartCutoff_mono y hab
    have h0 := chartCutoff_nonneg a y
    exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h1 h0 (h0.trans h1)) (hG0 y)
  have htend : ∀ y, Tendsto (fun k => f k y) atTop (𝓝 (ENNReal.ofReal (gradDens φ u u y))) := by
    intro y
    have h := ((tendsto_chartCutoff y).mul (tendsto_chartCutoff y)).mul_const (gradDens φ u u y)
    rw [one_mul, one_mul] at h
    exact (ENNReal.continuous_ofReal.tendsto _).comp h
  have hfm : ∀ k, AEMeasurable (f k) volume := fun k => (hψG k).1.aemeasurable.ennreal_ofReal
  have hlim := lintegral_tendsto_of_tendsto_of_monotone hfm (Eventually.of_forall hmono)
    (Eventually.of_forall htend)
  have hbd : ∀ k, ∫⁻ y, f k y ≤ ENNReal.ofReal (2 * I + 4 * U ^ 2 * K) := by
    intro k
    have hnn : ∀ y, 0 ≤ chartCutoff k y * chartCutoff k y * gradDens φ u u y := fun y =>
      mul_nonneg (mul_nonneg (chartCutoff_nonneg k y) (chartCutoff_nonneg k y)) (hG0 y)
    rw [hfdef, ← ofReal_integral_eq_lintegral_ofReal (hψG k) (Eventually.of_forall hnn)]
    exact ENNReal.ofReal_le_ofReal (hX k)
  refine ⟨hGc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hG0)]
  exact lt_of_le_of_lt (le_of_tendsto' hlim hbd) ENNReal.ofReal_lt_top

end

end GroundTheory.Heights₂.Heights
