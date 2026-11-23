import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory Set Complex Metric
open scoped ComplexConjugate Real

namespace UpperTheory.Esk.CayleyTransform

def cay (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)

theorem im_cay (w : ℂ) (hw : w ≠ 1) : (cay w).im = (1 - normSq w) / normSq (1 - w) := by
  have hn : normSq (1 - w) ≠ 0 := (normSq_pos.2 (sub_ne_zero.2 hw.symm)).ne'
  rw [cay, Complex.div_im]
  simp only [normSq_apply, mul_im, mul_re, I_re, I_im, add_re, add_im, one_re, one_im, sub_re, sub_im] at hn ⊢
  field_simp
  ring

theorem hasDerivAt_cay (w : ℂ) (hw : w ≠ 1) : HasDerivAt cay (2 * Complex.I / (1 - w) ^ 2) w := by
  have h1 : (1 - w) ≠ 0 := sub_ne_zero.2 hw.symm
  have := (((hasDerivAt_id w).const_add 1).const_mul Complex.I).div ((hasDerivAt_id w).const_sub 1) h1
  have hf : cay = (fun y => Complex.I * (1 + id y)) / (fun x => 1 - id x) := by
    funext x; simp [cay]
  rw [hf]
  refine this.congr_deriv ?_
  show (Complex.I * 1 * (1 - w) - Complex.I * (1 + w) * -1) / (1 - w) ^ 2 = 2 * Complex.I / (1 - w) ^ 2
  ring

theorem det_cay (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det = normSq c := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]

theorem ne_one_of_mem (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : w ≠ 1 := by
  rintro rfl; simp at hw

theorem normSq_lt_of_mem (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : normSq w < 1 := by
  rw [mem_ball_zero_iff] at hw
  rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]

theorem image_cay : cay '' ball (0 : ℂ) 1 = {t : ℂ | 0 < t.im} := by
  ext t
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h1 := ne_one_of_mem w hw
    have h2 := normSq_lt_of_mem w hw
    simp only [mem_ofPred_eq]
    rw [im_cay w h1]
    exact div_pos (by linarith) (normSq_pos.2 (sub_ne_zero.2 h1.symm))
  · intro ht
    simp only [mem_ofPred_eq] at ht
    have hd : t + Complex.I ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    refine ⟨(t - Complex.I) / (t + Complex.I), ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.2 hd)]
      rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
      simp only [normSq_apply, add_re, add_im, sub_re, sub_im, I_re, I_im]
      nlinarith
    · have h3 : 1 - (t - Complex.I) / (t + Complex.I) ≠ 0 := by
        rw [one_sub_div hd]; simp [hd]
      rw [cay, div_eq_iff h3]
      field_simp
      ring

theorem injOn_cay : InjOn cay (ball (0 : ℂ) 1) := by
  intro a ha b hb hab
  have h1 : 1 - a ≠ 0 := sub_ne_zero.2 (ne_one_of_mem a ha).symm
  have h2 : 1 - b ≠ 0 := sub_ne_zero.2 (ne_one_of_mem b hb).symm
  simp only [cay] at hab
  rw [div_eq_div_iff h1 h2] at hab
  have : Complex.I * (2 * (a - b)) = 0 := by linear_combination hab
  simpa [sub_eq_zero] using this

theorem step2 (g : ℂ → ℂ) (hg : IntegrableOn g {t : ℂ | 0 < t.im}) :
    IntegrableOn (fun w => ((4 / normSq (1 - w) ^ 2 : ℝ) : ℂ) * g (cay w)) (ball 0 1) ∧
    ∫ t in {t : ℂ | 0 < t.im}, g t = ∫ w in ball (0 : ℂ) 1, ((4 / normSq (1 - w) ^ 2 : ℝ) : ℂ) * g (cay w) := by
  have hs : MeasurableSet (ball (0 : ℂ) 1) := measurableSet_ball
  have hf' : ∀ w ∈ ball (0 : ℂ) 1, HasFDerivWithinAt cay
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ)
      (ball 0 1) w := fun w hw =>
    ((hasDerivAt_cay w (ne_one_of_mem w hw)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ w ∈ ball (0 : ℂ) 1,
      |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ).det|
        = 4 / normSq (1 - w) ^ 2 := by
    intro w hw
    rw [det_cay, abs_of_nonneg (normSq_nonneg _), map_div₀, map_pow, map_mul]
    simp [normSq_apply]
    norm_num
  have hpt : EqOn (fun w => |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ).det| • g (cay w))
      (fun w => ((4 / normSq (1 - w) ^ 2 : ℝ) : ℂ) * g (cay w)) (ball 0 1) := by
    intro w hw
    simp only
    rw [hdet w hw, Complex.real_smul]
  rw [← image_cay] at hg ⊢
  constructor
  · exact ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hf' injOn_cay g).1 hg).congr_fun
      hpt hs
  · rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs hf' injOn_cay]
    exact setIntegral_congr_fun hs hpt

theorem step1 (h : P → ℂ) (h0 : ∀ z : P, z.1.im < 0 → h z = 0) (hi : Integrable h) :
    IntegrableOn (fun t : ℂ => ((1 / t.im ^ 2 : ℝ) : ℂ) * ext1 h t) {t : ℂ | 0 < t.im} ∧
    ∫ z, h z = ∫ t in {t : ℂ | 0 < t.im}, ((1 / t.im ^ 2 : ℝ) : ℂ) * ext1 h t := by
  set S : Set ℂ := {t | t.im ≠ 0} with hSdef
  have hS : MeasurableSet S := (isOpen_ne_fun continuous_im continuous_const).measurableSet
  set g : ℂ → ℂ := fun t => ((1 / t.im ^ 2 : ℝ) : ℂ) * ext1 h t with hg
  have hρ : Measurable (fun z : S => ENNReal.ofReal (1 / z.1.im ^ 2)) := by fun_prop
  have hfin : ∀ᵐ z ∂(Measure.comap (Subtype.val : S → ℂ) volume), ENNReal.ofReal (1 / z.1.im ^ 2) < ⊤ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  set h' : S → ℂ := fun z => h ⟨z.1, z.2⟩ with hh'
  have key : (fun z : S => (ENNReal.ofReal (1 / z.1.im ^ 2)).toReal • h' z) = g ∘ Subtype.val := by
    funext z
    rw [ENNReal.toReal_ofReal (by positivity)]
    have hz : (z : ℂ).im ≠ 0 := z.2
    simp [g, ext1, hz, h', Complex.real_smul]
  have hi' : Integrable h'
      ((Measure.comap (Subtype.val : S → ℂ) volume).withDensity fun z => ENNReal.ofReal (1 / z.1.im ^ 2)) := hi
  have iS : IntegrableOn g S := by
    rw [integrableOn_iff_comap_subtypeVal hS, ← key]
    exact (integrable_withDensity_iff_integrable_smul' hρ hfin).1 hi'
  have hsub : {t : ℂ | 0 < t.im} ⊆ S := fun t ht => ne_of_gt ht
  refine ⟨iS.mono_set hsub, ?_⟩
  have e1 : ∫ z, h z = ∫ z : S, h' z ∂((Measure.comap (Subtype.val : S → ℂ) volume).withDensity
      fun z => ENNReal.ofReal (1 / z.1.im ^ 2)) := rfl
  rw [e1, integral_withDensity_eq_integral_toReal_smul hρ hfin, key]
  change ∫ z : S, g z ∂(Measure.comap Subtype.val volume) = _
  rw [integral_subtype_comap hS g]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (f := g) hS hsub ?_
  intro t ⟨ht1, ht2⟩
  have hlt : t.im < 0 := lt_of_le_of_ne (not_lt.1 ht2) ht1
  simp [g, ext1, h0 ⟨t, ht1⟩ hlt]

theorem step3 (F : ℂ → ℂ) (hF : IntegrableOn F (ball 0 1)) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F (circleMap 0 p.1 p.2)) (Ioo 0 1 ×ˢ Ioo (-π) π) ∧
    ∫ w in ball (0 : ℂ) 1, F w = ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π, (p.1 : ℂ) * F (circleMap 0 p.1 p.2) := by
  have hp : MeasurePreserving Complex.measurableEquivRealProd.symm volume volume :=
    Complex.volume_preserving_equiv_real_prod.symm
  have hSm : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := measurableSet_Ioo.prod measurableSet_Ioo
  have he : ∀ q : ℝ × ℝ, ‖Complex.measurableEquivRealProd.symm q‖ = √(q.1 ^ 2 + q.2 ^ 2) := by
    intro q
    change ‖Complex.equivRealProd.symm q‖ = _
    rw [Complex.equivRealProd_symm_apply, Complex.norm_def, Complex.normSq_add_mul_I]
  have hsub : polarCoord.symm '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) ⊆
      Complex.measurableEquivRealProd.symm ⁻¹' ball 0 1 := by
    rintro _ ⟨p, hp', rfl⟩
    simp only [mem_preimage, mem_ball_zero_iff]
    rw [measurableEquivRealProd_symm_polarCoord_symm_apply, norm_polarCoord_symm, abs_of_pos hp'.1.1]
    exact hp'.1.2
  have hae : polarCoord.symm '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) =ᵐ[volume]
      Complex.measurableEquivRealProd.symm ⁻¹' ball 0 1 := by
    filter_upwards [polarCoord_source_ae_eq_univ] with q hq
    have hq' : q ∈ polarCoord.source := by
      change polarCoord.source q
      rw [hq]; trivial
    apply propext
    constructor
    · exact fun h => hsub h
    · intro hqT
      have hm := polarCoord.map_source hq'
      refine ⟨polarCoord q, ⟨⟨hm.1, ?_⟩, hm.2⟩, polarCoord.left_inv hq'⟩
      change Complex.measurableEquivRealProd.symm q ∈ ball (0 : ℂ) 1 at hqT
      rw [mem_ball_zero_iff, he] at hqT
      simpa using hqT
  have hG : IntegrableOn (F ∘ Complex.measurableEquivRealProd.symm)
      (Complex.measurableEquivRealProd.symm ⁻¹' ball 0 1) :=
    (hp.integrableOn_comp_preimage Complex.measurableEquivRealProd.symm.measurableEmbedding).2 hF
  have hG' := hG.mono_set hsub
  have hder : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π,
      HasFDerivWithinAt polarCoord.symm (fderivPolarCoordSymm p) (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) p :=
    fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt
  have hinj : InjOn polarCoord.symm (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) :=
    polarCoord.symm.injOn.mono (fun p hp => show p ∈ polarCoord.target from ⟨hp.1.1, hp.2⟩)
  have hpt : EqOn (fun p : ℝ × ℝ => |(fderivPolarCoordSymm p).det| •
      (F ∘ Complex.measurableEquivRealProd.symm) (polarCoord.symm p))
      (fun p : ℝ × ℝ => (p.1 : ℂ) * F (circleMap 0 p.1 p.2)) (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := by
    intro p hp
    simp only
    rw [det_fderivPolarCoordSymm, abs_of_pos hp.1.1, Function.comp_apply,
      measurableEquivRealProd_symm_polarCoord_symm_apply, Complex.polarCoord_symm_apply,
      Complex.real_smul]
    congr 2
    rw [circleMap, zero_add, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  constructor
  · exact ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hSm hder hinj _).1 hG').congr_fun
      hpt hSm
  · rw [← hp.setIntegral_preimage_emb Complex.measurableEquivRealProd.symm.measurableEmbedding F (ball 0 1),
      ← setIntegral_congr_set hae,
      integral_image_eq_integral_abs_det_fderiv_smul volume hSm hder hinj]
    exact setIntegral_congr_fun hSm hpt

end UpperTheory.Esk.CayleyTransform

open UpperTheory.Esk.CayleyTransform in
theorem UpperTheory.Esk.cayley_transform_proof : UpperTheory.Esk.B2 := by
  intro h h0 hi
  obtain ⟨i1, e1⟩ := step1 h h0 hi
  obtain ⟨i2, e2⟩ := step2 _ i1
  set F : ℂ → ℂ := fun w => ((4 / (1 - normSq w) ^ 2 : ℝ) : ℂ) * ext1 h (cay w) with hF
  have eqD : EqOn (fun w => ((4 / normSq (1 - w) ^ 2 : ℝ) : ℂ) *
      (((1 / (cay w).im ^ 2 : ℝ) : ℂ) * ext1 h (cay w))) F (ball 0 1) := by
    intro w hw
    have hw1 : normSq w < 1 := by
      rw [mem_ball_zero_iff] at hw
      rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
    have hne : w ≠ 1 := by rintro rfl; simp at hw1
    have hn : 0 < normSq (1 - w) := normSq_pos.2 (sub_ne_zero.2 hne.symm)
    have h1 : 0 < 1 - normSq w := by linarith
    simp only [F]
    rw [im_cay w hne, ← mul_assoc, ← ofReal_mul]
    congr 2
    field_simp
  have i3 := i2.congr_fun eqD measurableSet_ball
  obtain ⟨i4, e4⟩ := step3 F i3
  have eqS : EqOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F (circleMap 0 p.1 p.2))
      (fun p : ℝ × ℝ => ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) *
        ext1 h (Complex.I * (1 + circleMap 0 p.1 p.2) / (1 - circleMap 0 p.1 p.2)))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hc : normSq (circleMap 0 r θ) = r ^ 2 := by
      rw [normSq_eq_norm_sq, norm_circleMap_zero, abs_of_pos hr.1]
    simp only [F, hc, cay]
    push_cast
    ring
  refine ⟨i4.congr_fun eqS (measurableSet_Ioo.prod measurableSet_Ioo), ?_⟩
  rw [e1, e2, setIntegral_congr_fun measurableSet_ball eqD, e4]
  exact setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) eqS
