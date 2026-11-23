import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsSphereLongitude
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsZonalReduction
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

theorem inner_spherePoint (c₁ φ₁ c₂ φ₂ : ℝ) :
    ⟪spherePoint c₁ φ₁, spherePoint c₂ φ₂⟫_ℝ =
      c₁ * c₂ + Real.sqrt (1 - c₁ ^ 2) * Real.sqrt (1 - c₂ ^ 2) * Real.cos (φ₂ - φ₁) := by
  simp [spherePoint, PiLp.inner_apply, Fin.sum_univ_three, Real.cos_sub]
  ring

theorem spherePoint_two (c φ : ℝ) : spherePoint c φ 2 = c := by
  simp [spherePoint]

theorem continuous_spherePoint : Continuous (fun q : ℝ × ℝ => spherePoint q.1 q.2) := by
  unfold spherePoint
  fun_prop

theorem measurable_kernelL : Measurable kernelL := by
  unfold kernelL
  exact measurable_const.mul (Real.measurable_log.comp ((measurable_const.sub measurable_id).div_const _))

theorem sqrt_mul_sqrt_le {c₁ c₂ : ℝ} (h₁ : c₁ ∈ Icc (-1 : ℝ) 1) (h₂ : c₂ ∈ Icc (-1 : ℝ) 1) :
    0 ≤ Real.sqrt (1 - c₁ ^ 2) * Real.sqrt (1 - c₂ ^ 2) ∧
    Real.sqrt (1 - c₁ ^ 2) * Real.sqrt (1 - c₂ ^ 2) ≤ 1 - c₁ * c₂ ∧
    Real.sqrt (1 - c₁ ^ 2) * Real.sqrt (1 - c₂ ^ 2) ≤ 1 + c₁ * c₂ ∧
    (c₁ ≠ c₂ → Real.sqrt (1 - c₁ ^ 2) * Real.sqrt (1 - c₂ ^ 2) < 1 - c₁ * c₂) := by
  obtain ⟨a₁, b₁⟩ := h₁
  obtain ⟨a₂, b₂⟩ := h₂
  have hs₁ : Real.sqrt (1 - c₁ ^ 2) ^ 2 = 1 - c₁ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs₂ : Real.sqrt (1 - c₂ ^ 2) ^ 2 = 1 - c₂ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hB2 : (Real.sqrt (1 - c₁ ^ 2) * Real.sqrt (1 - c₂ ^ 2)) ^ 2 = (1 - c₁ ^ 2) * (1 - c₂ ^ 2) := by
    rw [mul_pow, hs₁, hs₂]
  set B := Real.sqrt (1 - c₁ ^ 2) * Real.sqrt (1 - c₂ ^ 2)
  have hB : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hA : 0 ≤ 1 - c₁ * c₂ := by nlinarith
  have hA' : 0 ≤ 1 + c₁ * c₂ := by nlinarith
  refine ⟨hB, ?_, ?_, fun hne => ?_⟩
  · by_contra h
    rw [not_le] at h
    nlinarith [sq_nonneg (c₁ - c₂)]
  · by_contra h
    rw [not_le] at h
    nlinarith [sq_nonneg (c₁ + c₂)]
  · have hd : 0 < (c₁ - c₂) ^ 2 := by
      have : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
      positivity
    by_contra h
    rw [not_lt] at h
    nlinarith

theorem kernelL_spherePoint_nonpos {c₁ c₂ : ℝ} (h₁ : c₁ ∈ Icc (-1 : ℝ) 1)
    (h₂ : c₂ ∈ Icc (-1 : ℝ) 1) (φ₁ φ₂ : ℝ) :
    kernelL ⟪spherePoint c₁ φ₁, spherePoint c₂ φ₂⟫_ℝ ≤ 0 := by
  obtain ⟨hB, hB₁, hB₂, -⟩ := sqrt_mul_sqrt_le h₁ h₂
  set B := Real.sqrt (1 - c₁ ^ 2) * Real.sqrt (1 - c₂ ^ 2)
  have hc := Real.neg_one_le_cos (φ₂ - φ₁)
  have hc' := Real.cos_le_one (φ₂ - φ₁)
  rw [inner_spherePoint, kernelL]
  have e₁ : 0 ≤ (1 - (c₁ * c₂ + B * Real.cos (φ₂ - φ₁))) / 2 := by nlinarith
  have e₂ : (1 - (c₁ * c₂ + B * Real.cos (φ₂ - φ₁))) / 2 ≤ 1 := by nlinarith
  have := Real.log_nonpos e₁ e₂
  linarith

theorem continuous_kernelL_spherePoint {c₁ c₂ : ℝ} (h₁ : c₁ ∈ Icc (-1 : ℝ) 1)
    (h₂ : c₂ ∈ Icc (-1 : ℝ) 1) (hne : c₁ ≠ c₂) (φ₁ : ℝ) :
    Continuous (fun φ₂ => kernelL ⟪spherePoint c₁ φ₁, spherePoint c₂ φ₂⟫_ℝ) := by
  obtain ⟨hB, -, -, hlt⟩ := sqrt_mul_sqrt_le h₁ h₂
  have hlt := hlt hne
  set B := Real.sqrt (1 - c₁ ^ 2) * Real.sqrt (1 - c₂ ^ 2)
  simp only [inner_spherePoint, kernelL]
  refine continuous_const.mul (Continuous.log (by fun_prop) fun φ₂ => ?_)
  have hc' := Real.cos_le_one (φ₂ - φ₁)
  apply ne_of_gt
  nlinarith [mul_le_mul_of_nonneg_left hc' hB]

theorem integral_longitude (hK : ZonalKernel.Statement) {c₁ c₂ : ℝ} (h₁ : c₁ ∈ Icc (-1 : ℝ) 1)
    (h₂ : c₂ ∈ Icc (-1 : ℝ) 1) (hne : c₁ ≠ c₂) (φ₁ : ℝ) :
    IntegrableOn (fun φ₂ => kernelL ⟪spherePoint c₁ φ₁, spherePoint c₂ φ₂⟫_ℝ)
        (Ioc 0 (2 * Real.pi)) ∧
      ∫ φ₂ in Ioc 0 (2 * Real.pi), kernelL ⟪spherePoint c₁ φ₁, spherePoint c₂ φ₂⟫_ℝ =
        2 * Real.pi * zonalKernel c₁ c₂ := by
  have hcont := continuous_kernelL_spherePoint h₁ h₂ hne φ₁
  refine ⟨hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self, ?_⟩
  have hshift : ∀ φ₂, kernelL ⟪spherePoint c₁ φ₁, spherePoint c₂ φ₂⟫_ℝ =
      (fun φ => kernelL ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ) (φ₂ - φ₁) := by
    intro φ₂
    simp only [inner_spherePoint, sub_zero]
  have hper : Function.Periodic (fun φ => kernelL ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ)
      (2 * Real.pi) := by
    intro φ
    simp only [inner_spherePoint, sub_zero, Real.cos_add_two_pi]
  have e₁ := intervalIntegral.integral_comp_sub_right
    (fun φ => kernelL ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ) (a := 0) (b := 2 * Real.pi) φ₁
  have e₂ := hper.intervalIntegral_add_eq (0 - φ₁) 0
  have hk := hK c₁ h₁ c₂ h₂ hne
  rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le]
  simp_rw [hshift]
  rw [e₁, show 2 * Real.pi - φ₁ = 0 - φ₁ + 2 * Real.pi by ring, e₂, zero_add, ← hk]
  field_simp

theorem abs_zonalKernel_le {c₁ c₂ : ℝ} (h₁ : c₁ ∈ Ioo (-1 : ℝ) 1) (h₂ : c₂ ∈ Icc (-1 : ℝ) 1) :
    |zonalKernel c₁ c₂| ≤ -(1 / 2) * Real.log ((1 - c₁ ^ 2) / 4) := by
  obtain ⟨a₁, b₁⟩ := h₁
  obtain ⟨a₂, b₂⟩ := h₂
  have hmax₁ : c₁ ≤ max c₁ c₂ := le_max_left _ _
  have hmax₂ : max c₁ c₂ ≤ 1 := max_le b₁.le b₂
  have hmin₁ : min c₁ c₂ ≤ c₁ := min_le_left _ _
  have hmin₂ : -1 ≤ min c₁ c₂ := le_min a₁.le a₂
  have hpos : 0 < (1 - c₁ ^ 2) / 4 := by nlinarith
  have hle : (1 - c₁ ^ 2) / 4 ≤ (1 + max c₁ c₂) * (1 - min c₁ c₂) / 4 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + max c₁ c₂) (by linarith : 0 ≤ c₁ - min c₁ c₂),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - c₁) (by linarith : 0 ≤ max c₁ c₂ - c₁)]
  have hle₁ : (1 + max c₁ c₂) * (1 - min c₁ c₂) / 4 ≤ 1 := by
    nlinarith [mul_le_mul (by linarith : 1 + max c₁ c₂ ≤ 2) (by linarith : 1 - min c₁ c₂ ≤ 2)
      (by linarith) (by norm_num : (0 : ℝ) ≤ 2)]
  have l₁ := Real.log_le_log hpos hle
  have l₂ := Real.log_nonpos (hpos.le.trans hle) hle₁
  rw [zonalKernel, abs_of_nonpos (by linarith)]
  linarith

theorem integrableOn_log_one_sub_sq :
    IntegrableOn (fun c : ℝ => Real.log ((1 - c ^ 2) / 4)) (Icc (-1) 1) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioo]
  have i₁ : IntervalIntegrable (fun c => Real.log (1 - c)) volume (-1) 1 := by
    have := (intervalIntegral.intervalIntegrable_log' (a := 2) (b := 0)).comp_sub_left 1
    norm_num at this
    exact this
  have i₂ : IntervalIntegrable (fun c => Real.log (c + 1)) volume (-1) 1 := by
    have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 2)).comp_add_right 1
    norm_num at this
    exact this
  have i₃ : IntegrableOn (fun c => Real.log (1 - c) + Real.log (c + 1) - Real.log 4) (Ioo (-1) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp ((i₁.add i₂).sub intervalIntegrable_const)
  refine i₃.congr_fun (fun c hc => ?_) measurableSet_Ioo
  obtain ⟨a, b⟩ := hc
  rw [show (1 - c ^ 2) / 4 = (1 - c) * (c + 1) / 4 by ring,
    Real.log_div (by nlinarith) (by norm_num), Real.log_mul (by linarith) (by linarith)]

abbrev heightLongitudeMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))

theorem integral_kernelL_mul (hK : ZonalKernel.Statement) {c₁ : ℝ} (h₁ : c₁ ∈ Ioo (-1 : ℝ) 1)
    (φ₁ : ℝ) {h : ℝ → ℝ} (hh : Continuous h) :
    Integrable (fun q : ℝ × ℝ => kernelL ⟪spherePoint c₁ φ₁, spherePoint q.1 q.2⟫_ℝ * h q.1)
        heightLongitudeMeasure ∧
      ∫ q, kernelL ⟪spherePoint c₁ φ₁, spherePoint q.1 q.2⟫_ℝ * h q.1 ∂heightLongitudeMeasure =
        ∫ c₂ in Icc (-1 : ℝ) 1, 2 * Real.pi * zonalKernel c₁ c₂ * h c₂ := by
  have h₁' : c₁ ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self h₁
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c₁ := compl_mem_ae_iff.mpr (measure_singleton c₁)
  have hae : ∀ᵐ c₂ ∂(volume.restrict (Icc (-1 : ℝ) 1)), c₂ ∈ Icc (-1 : ℝ) 1 ∧ c₂ ≠ c₁ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with c₂ h h'
    exact ⟨h, h'⟩
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
    hh.continuousOn
  have hmeas : Measurable
      (fun q : ℝ × ℝ => kernelL ⟪spherePoint c₁ φ₁, spherePoint q.1 q.2⟫_ℝ * h q.1) :=
    (measurable_kernelL.comp
      ((continuous_const.inner continuous_spherePoint).measurable)).mul
      (hh.measurable.comp measurable_fst)
  have hint : Integrable
      (fun q : ℝ × ℝ => kernelL ⟪spherePoint c₁ φ₁, spherePoint q.1 q.2⟫_ℝ * h q.1)
      heightLongitudeMeasure := by
    rw [heightLongitudeMeasure, integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [hae] with c₂ hc₂
      exact (integral_longitude hK h₁' hc₂.1 hc₂.2.symm φ₁).1.mul_const (h c₂)
    · refine Integrable.mono'
        (integrable_const (2 * Real.pi * (-(1 / 2) * Real.log ((1 - c₁ ^ 2) / 4)) * M))
        hmeas.aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [hae] with c₂ hc₂
      have hl := (integral_longitude hK h₁' hc₂.1 hc₂.2.symm φ₁).2
      have hnp := kernelL_spherePoint_nonpos h₁' hc₂.1 φ₁
      have e : ∫ φ₂ in Ioc 0 (2 * Real.pi),
          ‖kernelL ⟪spherePoint c₁ φ₁, spherePoint (c₂, φ₂).1 (c₂, φ₂).2⟫_ℝ * h (c₂, φ₂).1‖ =
          -(2 * Real.pi * zonalKernel c₁ c₂) * |h c₂| := by
        rw [← hl, ← integral_neg, ← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun φ₂ => ?_)
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonpos (hnp φ₂)]
      rw [e]
      have hz := abs_zonalKernel_le h₁ hc₂.1
      have hM' : |h c₂| ≤ M := by simpa [Real.norm_eq_abs] using hM c₂ hc₂.1
      have hz' : -(2 * Real.pi * zonalKernel c₁ c₂) ≤
          2 * Real.pi * (-(1 / 2) * Real.log ((1 - c₁ ^ 2) / 4)) := by
        have := neg_abs_le (zonalKernel c₁ c₂)
        nlinarith [Real.pi_pos]
      have h0 : 0 ≤ -(2 * Real.pi * zonalKernel c₁ c₂) := by
        rw [← hl]
        exact neg_nonneg.mpr (setIntegral_nonpos measurableSet_Ioc fun φ₂ _ => hnp φ₂)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (abs_nonneg _))]
      exact mul_le_mul hz' hM' (abs_nonneg _) (h0.trans hz')
  refine ⟨hint, ?_⟩
  rw [heightLongitudeMeasure, integral_prod _ hint]
  refine integral_congr_ae ?_
  filter_upwards [hae] with c₂ hc₂
  rw [integral_mul_const, (integral_longitude hK h₁' hc₂.1 hc₂.2.symm φ₁).2]

theorem ZonalHeightReduction.proof (hA : SphereLongitudeCoordinates.Statement)
    (hK : ZonalKernel.Statement) : ZonalHeightReduction.Statement := by
  intro F H
  have : IsProbabilityMeasure sphereMeasure := ⟨sphereMeasure_univ⟩
  set μ := heightLongitudeMeasure with hμ
  have hsp : Measurable (fun q : ℝ × ℝ => spherePoint q.1 q.2) :=
    continuous_spherePoint.measurable
  have hι : Measurable (fun n : Sphere2 => (n : E3)) := measurable_subtype_coe
  set k : ENNReal := (ENNReal.ofReal (4 * Real.pi))⁻¹ with hk
  have hA' : sphereMeasure.map (fun n : Sphere2 => (n : E3)) =
      k • μ.map (fun q : ℝ × ℝ => spherePoint q.1 q.2) := by
    rw [hA, hμ, heightLongitudeMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hmap : pairMeasure.map (Prod.map (fun n : Sphere2 => (n : E3)) (fun n : Sphere2 => (n : E3))) =
      (k * k) • (μ.prod μ).map
        (Prod.map (fun q : ℝ × ℝ => spherePoint q.1 q.2) (fun q : ℝ × ℝ => spherePoint q.1 q.2)) := by
    rw [pairMeasure, ← Measure.map_prod_map _ _ hι hι, hA', Measure.prod_smul_left,
      Measure.prod_smul_right, Measure.map_prod_map _ _ hsp hsp, smul_smul]
  have h4 : ENNReal.ofReal (4 * Real.pi) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hk0 : k * k ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
      (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
  have hktop : k * k ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr h4) (ENNReal.inv_ne_top.mpr h4)
  set g : E3 × E3 → ℝ := fun x => kernelL ⟪x.1, x.2⟫_ℝ * F.eval (x.1 2) * H.eval (x.2 2) with hg
  have hgm : Measurable g := by
    have hF : Continuous (fun x : E3 × E3 => F.eval (x.1 2)) := by fun_prop
    have hH : Continuous (fun x : E3 × E3 => H.eval (x.2 2)) := by fun_prop
    exact ((measurable_kernelL.comp continuous_inner.measurable).mul hF.measurable).mul hH.measurable
  set ψ : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun q =>
    kernelL ⟪spherePoint q.1.1 q.1.2, spherePoint q.2.1 q.2.2⟫_ℝ * F.eval q.1.1 * H.eval q.2.1
    with hψdef
  have hgψ : g ∘ Prod.map (fun q : ℝ × ℝ => spherePoint q.1 q.2)
      (fun q : ℝ × ℝ => spherePoint q.1 q.2) = ψ := by
    funext q
    simp [hg, hψdef, spherePoint_two]
  have hψm : Measurable ψ := hgψ ▸ hgm.comp (hsp.prodMap hsp)
  have haeI : ∀ᵐ c ∂(volume.restrict (Icc (-1 : ℝ) 1)), c ∈ Ioo (-1 : ℝ) 1 :=
    ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Icc (ae_restrict_mem measurableSet_Ioo)
  have hae₁ : ∀ᵐ q ∂μ, q.1 ∈ Ioo (-1 : ℝ) 1 := Measure.quasiMeasurePreserving_fst.ae haeI
  have hae₂ : ∀ᵐ q ∂μ, q.1 ∈ Icc (-1 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  obtain ⟨MF, hMF⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
    F.continuous.continuousOn
  obtain ⟨MH, hMH⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
    H.continuous.continuousOn
  have hslice : ∀ q₁ : ℝ × ℝ, (fun q₂ => ψ (q₁, q₂)) = fun q₂ : ℝ × ℝ =>
      kernelL ⟪spherePoint q₁.1 q₁.2, spherePoint q₂.1 q₂.2⟫_ℝ * (F.eval q₁.1 * H.eval q₂.1) := by
    intro q₁
    funext q₂
    simp only [hψdef]
    ring
  have hψint : Integrable ψ (μ.prod μ) := by
    rw [integrable_prod_iff hψm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [hae₁] with q₁ hq₁
      rw [hslice q₁]
      exact (integral_kernelL_mul hK hq₁ q₁.2 (h := fun c₂ => F.eval q₁.1 * H.eval c₂)
        (by fun_prop)).1
    · have hw := (((((integrableOn_log_one_sub_sq.comp_fst
        (volume.restrict (Ioc 0 (2 * Real.pi)))).const_mul (-(1 / 2))).const_mul
        (2 * Real.pi)).mul_const (MF * MH)).mul_const 2)
      refine Integrable.mono' hw hψm.aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [hae₁] with q₁ hq₁
      have hq₁' := Ioo_subset_Icc_self hq₁
      have e : ∫ q₂, ‖ψ (q₁, q₂)‖ ∂μ = ∫ q₂, kernelL ⟪spherePoint q₁.1 q₁.2,
          spherePoint q₂.1 q₂.2⟫_ℝ * (-(|F.eval q₁.1| * |H.eval q₂.1|)) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hae₂] with q₂ hq₂
        have := kernelL_spherePoint_nonpos hq₁' hq₂ q₁.2 q₂.2
        simp only [hψdef, norm_mul, Real.norm_eq_abs, abs_of_nonpos this]
        ring
      rw [e, (integral_kernelL_mul hK hq₁ q₁.2 (h := fun c₂ => -(|F.eval q₁.1| * |H.eval c₂|))
        (by fun_prop)).2]
      refine (norm_setIntegral_le_of_norm_le_const_ae'
        (C := 2 * Real.pi * (-(1 / 2) * Real.log ((1 - q₁.1 ^ 2) / 4)) * (MF * MH))
        measure_Icc_lt_top (Filter.Eventually.of_forall fun c₂ hc₂ => ?_)).trans (le_of_eq ?_)
      · have hz := abs_zonalKernel_le hq₁ hc₂
        have hF : |F.eval q₁.1| ≤ MF := by simpa [Real.norm_eq_abs] using hMF q₁.1 hq₁'
        have hH : |H.eval c₂| ≤ MH := by simpa [Real.norm_eq_abs] using hMH c₂ hc₂
        simp only [norm_mul, norm_neg, Real.norm_eq_abs, abs_abs, abs_of_pos Real.pi_pos,
          abs_two]
        have hw0 : 0 ≤ -(1 / 2) * Real.log ((1 - q₁.1 ^ 2) / 4) := (abs_nonneg _).trans hz
        exact mul_le_mul (mul_le_mul_of_nonneg_left hz (by positivity))
          (mul_le_mul hF hH (abs_nonneg _) ((abs_nonneg _).trans hF)) (by positivity)
          (by positivity)
      · simp [measureReal_def, Real.volume_Icc]
        norm_num
  have hψval : ∫ q, ψ q ∂(μ.prod μ) = 4 * Real.pi ^ 2 *
      ∫ c₁ in (-1 : ℝ)..1, ∫ c₂ in (-1 : ℝ)..1, zonalKernel c₁ c₂ * F.eval c₁ * H.eval c₂ := by
    rw [integral_prod ψ hψint]
    have e : ∀ᵐ q₁ ∂μ, ∫ q₂, ψ (q₁, q₂) ∂μ = (fun c₁ => 2 * Real.pi *
        ∫ c₂ in (-1 : ℝ)..1, zonalKernel c₁ c₂ * F.eval c₁ * H.eval c₂) q₁.1 := by
      filter_upwards [hae₁] with q₁ hq₁
      rw [hslice q₁, (integral_kernelL_mul hK hq₁ q₁.2 (h := fun c₂ => F.eval q₁.1 * H.eval c₂)
        (by fun_prop)).2, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num), ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun c₂ _ => ?_
      ring
    rw [integral_congr_ae e, hμ, heightLongitudeMeasure, integral_fun_fst (fun c₁ : ℝ => 2 * Real.pi *
        ∫ c₂ in (-1 : ℝ)..1, zonalKernel c₁ c₂ * F.eval c₁ * H.eval c₂),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
      intervalIntegral.integral_const_mul]
    simp [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal, Real.pi_pos.le]
    ring
  have hf : (fun p : Sphere2 × Sphere2 => kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ *
      F.eval (height p.1) * H.eval (height p.2)) =
      g ∘ Prod.map (fun n : Sphere2 => (n : E3)) (fun n : Sphere2 => (n : E3)) := rfl
  have hT := hsp.prodMap hsp
  have hI := hι.prodMap hι
  rw [hf]
  constructor
  · rw [← integrable_map_measure hgm.aestronglyMeasurable hI.aemeasurable, hmap,
      integrable_smul_measure hk0 hktop,
      integrable_map_measure hgm.aestronglyMeasurable hT.aemeasurable, hgψ]
    exact hψint
  · calc ∫ p, (g ∘ Prod.map (fun n : Sphere2 => (n : E3)) (fun n : Sphere2 => (n : E3))) p
          ∂pairMeasure
        = ∫ x, g x ∂(pairMeasure.map
            (Prod.map (fun n : Sphere2 => (n : E3)) (fun n : Sphere2 => (n : E3)))) :=
          (integral_map hI.aemeasurable hgm.aestronglyMeasurable).symm
      _ = (k * k).toReal • ∫ q, (g ∘ Prod.map (fun q : ℝ × ℝ => spherePoint q.1 q.2)
            (fun q : ℝ × ℝ => spherePoint q.1 q.2)) q ∂(μ.prod μ) := by
          rw [hmap, integral_smul_measure, integral_map hT.aemeasurable hgm.aestronglyMeasurable]
          rfl
      _ = (k * k).toReal • ∫ q, ψ q ∂(μ.prod μ) := by rw [hgψ]
      _ = _ := by
          rw [hψval, hk, ENNReal.toReal_mul, ENNReal.toReal_inv,
            ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
          field_simp

end

end GroundTheory.Heights₂.Heights.FlagBundles
