import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFderivChiBound

open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

section Wirt

theorem dZ_eq (f : ℂ → ℂ) (c : ℂ) : NF.dZ f c = (1 / 2 : ℂ) * (fderiv ℝ f c 1 - Complex.I * fderiv ℝ f c Complex.I) := rfl

theorem dZ_conj {φ : ℂ → ℂ} {c : ℂ} (h : DifferentiableAt ℝ φ c) :
    NF.dZ (fun w => conj (φ w)) c = conj (NF.dZb φ c) := by
  have hd : HasFDerivAt (fun w => conj (φ w)) ((Complex.conjCLE.toContinuousLinearMap).comp (fderiv ℝ φ c)) c :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp c h.hasFDerivAt
  unfold NF.dZ NF.dZb
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul,
    map_add, map_sub, Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring

theorem dZb_div {g : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) (h : DifferentiableAt ℝ g c) :
    NF.dZb (fun w => g w / w) c = NF.dZb g c / c := by
  have hinv := (hasDerivAt_inv hc).hasFDerivAt.restrictScalars ℝ
  have hprod : HasFDerivAt (fun w => g w * w⁻¹) _ c := h.hasFDerivAt.mul hinv
  have he : (fun w => g w / w) = fun w => g w * w⁻¹ := by funext w; rw [div_eq_mul_inv]
  unfold NF.dZb
  rw [he, hprod.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  field_simp
  linear_combination (-(g c)) * Complex.I_sq

end Wirt

section IBP

theorem int_dZ_mul (f G : ℂ → ℂ)
    (hf : ∀ x ∈ tsupport G, DifferentiableAt ℝ f x) (hG : ∀ x ∈ tsupport f, DifferentiableAt ℝ G x)
    (h1 : Integrable (fun x => fderiv ℝ f x 1 * G x)) (h2 : Integrable (fun x => f x * fderiv ℝ G x 1))
    (h3 : Integrable (fun x => fderiv ℝ f x Complex.I * G x))
    (h4 : Integrable (fun x => f x * fderiv ℝ G x Complex.I)) (h5 : Integrable (fun x => f x * G x)) :
    ∫ x, NF.dZ f x * G x = -∫ x, f x * NF.dZ G x := by
  have e1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := (1 : ℂ)) h1 h2 h5 hf hG
  have e2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := Complex.I) h3 h4 h5 hf hG
  have l1 : ∫ x, NF.dZ f x * G x =
      (1 / 2 : ℂ) * ((∫ x, fderiv ℝ f x 1 * G x) - Complex.I * ∫ x, fderiv ℝ f x Complex.I * G x) := by
    rw [← integral_const_mul, ← integral_sub h1 (h3.const_mul _), ← integral_const_mul]
    congr 1; funext x; unfold NF.dZ; ring
  have l2 : ∫ x, f x * NF.dZ G x =
      (1 / 2 : ℂ) * ((∫ x, f x * fderiv ℝ G x 1) - Complex.I * ∫ x, f x * fderiv ℝ G x Complex.I) := by
    rw [← integral_const_mul, ← integral_sub h2 (h4.const_mul _), ← integral_const_mul]
    congr 1; funext x; unfold NF.dZ; ring
  rw [l1, l2, e1, e2]
  ring

end IBP

section Cpt

theorem int_mul_of_cpt {a b : ℂ → ℂ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hU : tsupport a ⊆ {c | c ≠ 0}) (hb : ContinuousOn b {c | c ≠ 0}) : Integrable (fun x => a x * b x) := by
  have hcont : Continuous (fun x => a x * b x) := by
    refine ContinuousOn.continuous_of_tsupport_subset (ha.continuousOn.mul hb) isOpen_ne ?_
    exact (tsupport_mul_subset_left).trans hU
  exact hcont.integrable_of_hasCompactSupport hac.mul_right

theorem pLogAdj_cpt (f g : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (hf0 : (0 : ℂ) ∉ tsupport f)
    (hg : ContDiffOn ℝ 1 g {c | c ≠ 0}) :
    ∫ c, c * NF.dZ f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ) =
      -∫ c, f c * conj (conj c * NF.dZb g c) / ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  set U : Set ℂ := {c | c ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne
  have hfU : tsupport f ⊆ U := fun x hx h => hf0 (h ▸ hx)
  set G : ℂ → ℂ := fun w => conj (g w / w) with hGdef
  have hinv : ContDiffOn ℝ 1 (fun w : ℂ => w⁻¹) U := fun x hx => (contDiffAt_inv ℝ hx).contDiffWithinAt
  have hq : ContDiffOn ℝ 1 (fun w => g w / w) U := by
    have := hg.mul hinv
    simpa only [div_eq_mul_inv] using this
  have hGc : ContDiffOn ℝ 1 G U := Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hq
  have hGd : ∀ x ∈ U, DifferentiableAt ℝ G x := fun x hx =>
    (hGc.differentiableOn one_ne_zero x hx).differentiableAt (hUo.mem_nhds hx)
  have hgd : ∀ x ∈ U, DifferentiableAt ℝ g x := fun x hx =>
    (hg.differentiableOn one_ne_zero x hx).differentiableAt (hUo.mem_nhds hx)
  have hqd : ∀ x ∈ U, DifferentiableAt ℝ (fun w => g w / w) x := fun x hx =>
    (hq.differentiableOn one_ne_zero x hx).differentiableAt (hUo.mem_nhds hx)
  have hGf : ContinuousOn (fderiv ℝ G) U := hGc.continuousOn_fderiv_of_isOpen hUo le_rfl
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hff : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hDf : ∀ v : ℂ, Continuous (fun x => fderiv ℝ f x v) ∧ HasCompactSupport (fun x => fderiv ℝ f x v) ∧
      tsupport (fun x => fderiv ℝ f x v) ⊆ U := by
    intro v
    have h0 : (fun L : ℂ →L[ℝ] ℂ => L v) 0 = 0 := rfl
    refine ⟨hff.clm_apply continuous_const,
      HasCompactSupport.comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) (hfc.fderiv (𝕜 := ℝ)) h0, ?_⟩
    exact ((tsupport_comp_subset (g := fun L : ℂ →L[ℝ] ℂ => L v) h0 (fderiv ℝ f)).trans
      (tsupport_fderiv_subset ℝ (f := f))).trans hfU
  have hGv : ∀ v : ℂ, ContinuousOn (fun x => fderiv ℝ G x v) U := fun v => hGf.clm_apply continuousOn_const
  have e := int_dZ_mul f G (fun x _ => hfd x) (fun x hx => hGd x (hfU hx))
    (int_mul_of_cpt (hDf 1).1 (hDf 1).2.1 (hDf 1).2.2 hGc.continuousOn)
    (int_mul_of_cpt hf.continuous hfc hfU (hGv 1))
    (int_mul_of_cpt (hDf Complex.I).1 (hDf Complex.I).2.1 (hDf Complex.I).2.2 hGc.continuousOn)
    (int_mul_of_cpt hf.continuous hfc hfU (hGv Complex.I))
    (int_mul_of_cpt hf.continuous hfc hfU hGc.continuousOn)
  have hL : (fun c => c * NF.dZ f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) = fun c => NF.dZ f c * G c := by
    funext c
    by_cases hc : c = 0
    · subst hc; simp [hGdef]
    · have hcc : conj c ≠ 0 := (map_ne_zero _).mpr hc
      have hn : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * conj c := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hn, hGdef]
      simp only [map_div₀]
      field_simp
  have hR : (fun c => f c * conj (conj c * NF.dZb g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) = fun c => f c * NF.dZ G c := by
    funext c
    by_cases hc : c = 0
    · subst hc
      have : f 0 = 0 := image_eq_zero_of_notMem_tsupport hf0
      simp [this]
    · have hcc : conj c ≠ 0 := (map_ne_zero _).mpr hc
      have hn : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * conj c := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hdG : NF.dZ G c = conj (NF.dZb g c) / conj c := by
        rw [hGdef, dZ_conj (hqd c hc), dZb_div hc (hgd c hc), map_div₀]
      rw [hn, hdG, map_mul, Complex.conj_conj]
      field_simp
  rw [hL, hR]
  exact e

end Cpt

end Formalism.FourierDecayAlt.P5.HerB
