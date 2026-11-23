import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralEqIteratedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumParsevalQExpansionHorizontalLineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem im_ofComplex_xy (x y : ℝ) (hy : 0 < y) :
    (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by
  have h : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  rw [ofComplex_apply_of_im_pos h]
  change ((x : ℂ) + (y : ℂ) * Complex.I).im = y
  simp

theorem integrableOn_rpow_sub_two_mul_exp_Ioi_one (r c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => y ^ (r - 2) * Real.exp (-c * y)) (Set.Ioi 1) := by
  have hI : IntegrableOn (fun y : ℝ => y ^ (max (r - 2) 0) * Real.exp (-c * y ^ (1 : ℝ)))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by have := le_max_right (r - 2) 0; linarith)
      one_pos hc
  have hI' := hI.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  refine Integrable.mono' hI' ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_)
    have hy1 : (1 : ℝ) ≤ y := le_of_lt hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hy0.le _)
      (Real.exp_pos _).le), Real.rpow_one]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hy1 (le_max_left _ _)) (Real.exp_pos _).le

theorem integrableOn_im_rpow_mul_exp_strip_one_le :
    ∀ (r c : ℝ), 0 < c → IntegrableOn (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im))
      {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
  intro r c hc
  have hmim : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hmeas : Measurable (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im)) :=
    (hmim.pow_const r).mul (Real.measurable_exp.comp (measurable_const.mul hmim))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hmT : MeasurableSet {τ : ℍ | 1 ≤ τ.im} := measurableSet_le measurable_const hmim
  have hS : {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im} = {τ : ℍ | 1 ≤ τ.im} ∩ strip := by
    ext τ; simp [and_comm]
  show ∫⁻ τ in {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im}, ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ < ⊤
  rw [hS, ← Measure.restrict_restrict hmT, ← lintegral_indicator hmT,
    (GlobalTheory.T.unitStrip_integral_eq_iterated).1 _ ((hmeas.enorm).indicator hmT)]
  have hinner : Set.EqOn
      (fun y : ℝ => (∫⁻ x in Set.Ico (0 : ℝ) 1, {τ : ℍ | 1 ≤ τ.im}.indicator
        (fun τ => ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ) (ofComplex (x + y * Complex.I))) *
          ENNReal.ofReal (1 / y ^ 2))
      (fun y : ℝ => (Set.Ici (1 : ℝ)).indicator
        (fun y => ENNReal.ofReal (y ^ (r - 2) * Real.exp (-c * y))) y) (Set.Ioi 0) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hpt : ∀ x : ℝ, {τ : ℍ | 1 ≤ τ.im}.indicator
        (fun τ => ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ) (ofComplex (x + y * Complex.I)) =
        (Set.Ici (1 : ℝ)).indicator
          (fun y => ENNReal.ofReal (y ^ r * Real.exp (-c * y))) y := by
      intro x
      by_cases h1 : (1 : ℝ) ≤ y
      · rw [Set.indicator_of_mem (by simpa [im_ofComplex_xy x y hy0] using h1),
          Set.indicator_of_mem (by simpa using h1), im_ofComplex_xy x y hy0,
          Real.enorm_eq_ofReal (mul_nonneg (Real.rpow_nonneg hy0.le _) (Real.exp_pos _).le)]
      · rw [Set.indicator_of_notMem (by simpa [im_ofComplex_xy x y hy0] using h1),
          Set.indicator_of_notMem (by simpa using h1)]
    simp only [hpt]
    rw [setLIntegral_const, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, mul_one]
    by_cases h1 : (1 : ℝ) ≤ y
    · rw [Set.indicator_of_mem (by simpa using h1), Set.indicator_of_mem (by simpa using h1),
        ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hy0.le _) (Real.exp_pos _).le)]
      congr 1
      rw [Real.rpow_sub hy0, Real.rpow_two]
      field_simp
    · rw [Set.indicator_of_notMem (by simpa using h1), Set.indicator_of_notMem (by simpa using h1),
        zero_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner, lintegral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici,
    Set.inter_eq_left.2 (Set.Ici_subset_Ioi.2 one_pos)]
  have hfin := ((integrableOn_Ici_iff_integrableOn_Ioi).2
    (integrableOn_rpow_sub_two_mul_exp_Ioi_one r c hc)).hasFiniteIntegral
  exact lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hfin

end GlobalTheory.EisM
