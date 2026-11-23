import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Metric Set Filter Topology
open scoped Interval

noncomputable section

def coordScale {D : ℕ} (i : Fin D) (t : ℝ) : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) :=
  ContinuousLinearMap.id ℂ _ +
    ((t : ℂ) - 1) • (ContinuousLinearMap.proj i : (Fin D → ℂ) →L[ℂ] ℂ).smulRight (Pi.single i (1 : ℂ))

variable {D : ℕ}

theorem coordScale_apply (i : Fin D) (t : ℝ) (v : Fin D → ℂ) (j : Fin D) :
    coordScale i t v j = if j = i then (t : ℂ) * v i else v j := by
  simp only [coordScale]
  simp only [Pi.single_apply, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
    Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  split_ifs <;> subst_vars <;> ring

theorem coordScale_of_eq_zero (i : Fin D) (t : ℝ) {v : Fin D → ℂ} (hv : v i = 0) : coordScale i t v = v := by
  funext j; rw [coordScale_apply]; split_ifs with h
  · subst h; simp [hv]
  · rfl

theorem coordScale_one (i : Fin D) (v : Fin D → ℂ) : coordScale i 1 v = v := by
  funext j; rw [coordScale_apply]; split_ifs with h
  · subst h; simp
  · rfl

theorem norm_coordScale_apply_le (i : Fin D) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (v : Fin D → ℂ) :
    ‖coordScale i t v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun j => ?_
  rw [coordScale_apply]
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans (norm_le_pi_norm v i)
  · exact norm_le_pi_norm v j

theorem norm_coordScale_le (i : Fin D) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖coordScale i t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simpa using norm_coordScale_apply_le i ht v

theorem coordScale_mem_ball (i : Fin D) {p z : Fin D → ℂ} {r t : ℝ} (hp : p i = 0) (hz : z ∈ ball p r)
    (ht : t ∈ Icc (0 : ℝ) 1) : coordScale i t z ∈ ball p r := by
  rw [mem_ball, dist_eq_norm] at hz ⊢
  calc ‖coordScale i t z - p‖ = ‖coordScale i t (z - p)‖ := by
        rw [map_sub, coordScale_of_eq_zero i t hp]
    _ ≤ ‖z - p‖ := norm_coordScale_apply_le i ht _
    _ < r := hz

theorem hasDerivAt_coordScale (i : Fin D) (z : Fin D → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => coordScale i s z) (z i • Pi.single i (1 : ℂ)) t := by
  have h := (((hasDerivAt_id t).ofReal_comp.sub_const (1 : ℂ)).smul_const
    (z i • Pi.single i (1 : ℂ) : Fin D → ℂ)).const_add z
  refine (h.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  funext j
  show coordScale i s z j = _
  rw [coordScale_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, id_eq]
  split_ifs <;> subst_vars <;> ring

theorem continuous_coordScale (i : Fin D) : Continuous (coordScale (D := D) i) :=
  continuous_const.add (((Complex.continuous_ofReal).sub continuous_const).smul continuous_const)

theorem analyticOnNhd_fderiv_apply {Ω : Set (Fin D → ℂ)} {F : (Fin D → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F Ω)
    (v : Fin D → ℂ) : AnalyticOnNhd ℂ (fun w => fderiv ℂ F w v) Ω := fun w hw =>
  (((ContinuousLinearMap.apply ℂ ℂ (E := Fin D → ℂ) v).analyticAt (fderiv ℂ F w)).comp
    (hF.fderiv w hw)).congr (Eventually.of_forall fun _ => rfl)

theorem eq_mul_integral_partial {Ω : Set (Fin D → ℂ)} {F : (Fin D → ℂ) → ℂ} {i : Fin D}
    (hF : AnalyticOnNhd ℂ F Ω) (h0 : ∀ z ∈ Ω, z i = 0 → F z = 0) {p : Fin D → ℂ} {r : ℝ}
    (hp : p i = 0) (hball : ball p r ⊆ Ω) {z : Fin D → ℂ} (hz : z ∈ ball p r) :
    F z = z i * ∫ t in (0 : ℝ)..1, fderiv ℂ F (coordScale i t z) (Pi.single i 1) := by
  have hFi : AnalyticOnNhd ℂ (fun w => fderiv ℂ F w (Pi.single i 1)) Ω := analyticOnNhd_fderiv_apply hF _
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, coordScale i t z ∈ Ω := fun t ht => hball (coordScale_mem_ball i hp hz ht)
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => F (coordScale i s z))
      (z i * fderiv ℂ F (coordScale i t z) (Pi.single i 1)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h1 := ((hF _ (hmem t ht)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      (hasDerivAt_coordScale i z t)
    refine h1.congr_deriv ?_
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  have hc : ContinuousOn (fun t : ℝ => z i * fderiv ℂ F (coordScale i t z) (Pi.single i 1)) (uIcc 0 1) := by
    refine continuousOn_const.mul (hFi.continuousOn.comp
      ((continuous_coordScale i).clm_apply continuous_const).continuousOn fun t ht => hmem t ?_)
    rwa [uIcc_of_le zero_le_one] at ht
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  rw [intervalIntegral.integral_const_mul, coordScale_one,
    h0 _ (hmem 0 ⟨le_rfl, zero_le_one⟩) (by simp [coordScale_apply])] at h
  rw [h, sub_zero]

theorem differentiableOn_integral_partial {Ω : Set (Fin D → ℂ)} {F : (Fin D → ℂ) → ℂ} {i : Fin D}
    (hF : AnalyticOnNhd ℂ F Ω) {p : Fin D → ℂ} {r : ℝ} (hp : p i = 0) (hball : ball p r ⊆ Ω) (hr : 0 < r) :
    DifferentiableOn ℂ (fun z => ∫ t in (0 : ℝ)..1, fderiv ℂ F (coordScale i t z) (Pi.single i 1))
      (ball p (r / 2)) := by
  set Fi : (Fin D → ℂ) → ℂ := fun w => fderiv ℂ F w (Pi.single i 1)
  have hFi : AnalyticOnNhd ℂ Fi Ω := analyticOnNhd_fderiv_apply hF _
  have hK : closedBall p (r / 2) ⊆ Ω := (closedBall_subset_ball (half_lt_self hr)).trans hball
  have hB : ball p (r / 2) ⊆ Ω := ball_subset_closedBall.trans hK
  obtain ⟨C, hC⟩ := (isCompact_closedBall p (r / 2)).exists_bound_of_continuousOn
    (hFi.fderiv.continuousOn.mono hK)
  have hI : ∀ {t : ℝ}, t ∈ Ι (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 := fun ht =>
    Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at ht)
  have hmem : ∀ x ∈ ball p (r / 2), ∀ t ∈ Icc (0 : ℝ) 1, coordScale i t x ∈ ball p (r / 2) :=
    fun x hx t ht => coordScale_mem_ball i hp hx ht
  have hcont : ∀ x ∈ ball p (r / 2), ContinuousOn (fun t : ℝ => Fi (coordScale i t x)) (Icc 0 1) :=
    fun x hx => hFi.continuousOn.comp ((continuous_coordScale i).clm_apply continuous_const).continuousOn
      fun t ht => hB (hmem x hx t ht)
  intro x₀ hx₀
  refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := MeasureTheory.volume)
    (F' := fun x t => (fderiv ℂ Fi (coordScale i t x)).comp (coordScale i t)) (bound := fun _ => C)
    (isOpen_ball.mem_nhds hx₀) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).differentiableAt.differentiableWithinAt
  · filter_upwards [isOpen_ball.mem_nhds hx₀] with x hx
    exact ((hcont x hx).mono fun t ht => hI ht).aestronglyMeasurable measurableSet_uIoc
  · exact (hcont x₀ hx₀).intervalIntegrable_of_Icc zero_le_one
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    exact ((hFi.fderiv.continuousOn.comp ((continuous_coordScale i).clm_apply continuous_const).continuousOn
      fun t ht => hB (hmem x₀ hx₀ t (hI ht))).clm_comp (continuous_coordScale i).continuousOn)
  · refine Eventually.of_forall fun t ht x hx => ?_
    calc ‖(fderiv ℂ Fi (coordScale i t x)).comp (coordScale i t)‖
        ≤ ‖fderiv ℂ Fi (coordScale i t x)‖ * ‖coordScale i t‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := mul_le_mul (hC _ (ball_subset_closedBall (hmem x hx t (hI ht))))
          (norm_coordScale_le i (hI ht)) (norm_nonneg _)
          ((norm_nonneg _).trans (hC p (mem_closedBall_self (half_pos hr).le)))
      _ = C := mul_one C
  · refine Eventually.of_forall fun t ht x hx => ?_
    exact (hFi _ (hB (hmem x hx t (hI ht)))).differentiableAt.hasFDerivAt.comp x (coordScale i t).hasFDerivAt

theorem HyperplaneDivisible.proof : HyperplaneDivisible.Statement := by
  intro D Ω F i hΩ hF h0
  set Fi : (Fin D → ℂ) → ℂ := fun w => fderiv ℂ F w (Pi.single i 1)
  refine ⟨fun z => if z i = 0 then Fi z else F z / z i, fun p hp => ?_, fun z hz => ?_⟩
  · by_cases hpi : p i = 0
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ p hp
      have hH := ReciprocityTheory.AnForm.Osgood.osgood D _ _ isOpen_ball
        (differentiableOn_integral_partial hF hpi hball hr) p (mem_ball_self (half_pos hr))
      refine hH.congr ?_
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (half_pos hr))] with z hz
      have hz' : z ∈ ball p r := ball_subset_ball (half_le_self hr.le) hz
      by_cases hzi : z i = 0
      · simp only [if_pos hzi, coordScale_of_eq_zero i _ hzi, intervalIntegral.integral_const, Fi]
        simp
      · rw [if_neg hzi, eq_mul_integral_partial hF h0 hpi hball hz', mul_div_cancel_left₀ _ hzi]
    · have hproj : AnalyticAt ℂ (fun z : Fin D → ℂ => z i) p :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt p
      refine ((hF p hp).div hproj hpi).congr ?_
      filter_upwards [(isOpen_ne_fun (continuous_apply i) continuous_const).mem_nhds hpi] with z hz
      simp only [if_neg (show z i ≠ 0 from hz)]
      rfl
  · by_cases hzi : z i = 0
    · simp [hzi, h0 z hz hzi]
    · simp only [if_neg hzi]
      rw [mul_div_cancel₀ _ hzi]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
