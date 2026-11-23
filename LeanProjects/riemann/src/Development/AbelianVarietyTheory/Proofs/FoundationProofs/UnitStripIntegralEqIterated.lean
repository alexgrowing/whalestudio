import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

def ptXY (p : ℝ × ℝ) : ℍ := ofComplex ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)

theorem measurable_ofComplex_hp : Measurable (ofComplex : ℂ → ℍ) := by
  classical
  rw [← measurableEmbedding_coe.measurable_comp_iff]
  have h : (UpperHalfPlane.coe ∘ (ofComplex : ℂ → ℍ)) =
      fun w : ℂ => if 0 < w.im then w else ((ofComplex 0 : ℍ) : ℂ) := by
    funext w
    by_cases hw : 0 < w.im
    · simp [hw, ofComplex_apply_of_im_pos hw]
    · simp only [Function.comp, hw, if_false]
      rw [ofComplex_apply_of_im_nonpos (not_lt.mp hw),
        ofComplex_apply_of_im_nonpos (le_refl _ : (0 : ℂ).im ≤ 0)]
  rw [h]
  exact Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im) measurable_id
    measurable_const

theorem ptXY_eq (p : ℝ × ℝ) : ptXY p = ofComplex (Complex.measurableEquivRealProd.symm p) := by
  unfold ptXY
  congr 1
  apply Complex.ext <;> simp

theorem measurable_ptXY : Measurable ptXY := by
  simp only [funext ptXY_eq]
  exact measurable_ofComplex_hp.comp Complex.measurableEquivRealProd.symm.measurable

theorem volume_eq_map_ptXY : (volume : Measure ℍ) = Measure.map ptXY
    (((volume : Measure ℝ).prod (volume.restrict (Set.Ioi 0))).withDensity
      fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  have hm := measurable_ptXY
  ext s hs
  have hp : (volume : Measure ℝ).prod (volume.restrict (Set.Ioi (0 : ℝ))) =
      (volume : Measure (ℝ × ℝ)).restrict (Set.univ ×ˢ Set.Ioi 0) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hset : ptXY ⁻¹' s ∩ Set.univ ×ˢ Set.Ioi 0 =
      Complex.measurableEquivRealProd.symm ⁻¹' (UpperHalfPlane.coe '' s) := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_Ioi, Set.mem_image, ptXY_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by simpa using h2
      refine ⟨_, h1, ?_⟩
      rw [ofComplex_apply_of_im_pos h3]
    · rintro ⟨z, hz, hzp⟩
      refine ⟨?_, ?_⟩
      · rw [← hzp, ofComplex_apply]; exact hz
      · have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by
          rw [← hzp]; exact z.im_pos
        simpa using h3
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), hp, Measure.restrict_restrict (hm hs), hset,
    volume_eq_lintegral,
    ← (Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
  refine lintegral_congr fun p => ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp

theorem measurableSet_strip : MeasurableSet strip := by
  have h : strip = (fun z : ℍ => z.re) ⁻¹' (Set.Ico 0 1) := rfl
  rw [h]
  exact UpperHalfPlane.continuous_re.measurable measurableSet_Ico

theorem ptXY_re (x y : ℝ) (hy : 0 < y) : (ptXY (x, y)).re = x := by
  have h : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  rw [ptXY, ofComplex_apply_of_im_pos h]
  simp [UpperHalfPlane.re]

theorem restrict_strip_eq_map : (volume : Measure ℍ).restrict strip = Measure.map ptXY
    ((((volume : Measure ℝ).restrict (Set.Ico 0 1)).prod (volume.restrict (Set.Ioi 0))).withDensity
      fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  have hm := measurable_ptXY
  have hS := hm measurableSet_strip
  have h1 : ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Set.Ioi 0) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have h2 : ptXY ⁻¹' strip ∩ Set.univ ×ˢ Set.Ioi 0 = Set.Ico 0 1 ×ˢ Set.Ioi 0 := by
    ext ⟨x, y⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_Ioi, Set.mem_Ico, strip, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h, hy⟩
      rw [ptXY_re x y hy] at h
      exact ⟨h, hy⟩
    · rintro ⟨h, hy⟩
      rw [ptXY_re x y hy]
      exact ⟨h, hy⟩
  rw [volume_eq_map_ptXY, Measure.restrict_map hm measurableSet_strip, restrict_withDensity hS, h1,
    Measure.restrict_restrict hS, h2, Measure.prod_restrict]

theorem strip_iterated :
    (∀ F : ℍ → ENNReal, Measurable F → ∫⁻ τ in strip, F τ = ∫⁻ y in Set.Ioi (0 : ℝ),
      (∫⁻ x in Set.Ico (0 : ℝ) 1, F (ofComplex (x + y * Complex.I))) * ENNReal.ofReal (1 / y ^ 2)) ∧
    ∀ F : ℍ → ℂ, IntegrableOn F strip → ∫ τ in strip, F τ = ∫ y in Set.Ioi (0 : ℝ),
      (∫ x in (0 : ℝ)..1, F (ofComplex (x + y * Complex.I))) / (y : ℂ) ^ 2 := by
  have hm := measurable_ptXY
  have hd : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2)) := by fun_prop
  refine ⟨fun F hF => ?_, fun H hH => ?_⟩
  · rw [restrict_strip_eq_map, lintegral_map hF hm, lintegral_withDensity_eq_lintegral_mul _ hd (g := fun a => F (ptXY a)) (hF.comp hm)]
    simp only [Pi.mul_apply]
    rw [lintegral_prod_symm (fun a => ENNReal.ofReal (1 / a.2 ^ 2) * F (ptXY a))
      ((hd.mul (hF.comp hm)).aemeasurable)]
    refine lintegral_congr fun y => ?_
    rw [lintegral_const_mul (ENNReal.ofReal (1 / y ^ 2)) (f := fun x : ℝ => F (ptXY (x, y)))
      (hF.comp (hm.comp (measurable_id.prodMk measurable_const))), mul_comm]
    rfl
  · unfold IntegrableOn at hH
    rw [restrict_strip_eq_map] at hH ⊢
    have hI := (integrable_map_measure hH.1 hm.aemeasurable).1 hH
    rw [integral_map hm.aemeasurable hH.1,
      integral_withDensity_eq_integral_toReal_smul hd (by simp)]
    rw [integrable_withDensity_iff_integrable_smul' hd (by simp)] at hI
    have key : ∀ y : ℝ, ∫ x in Set.Ico (0 : ℝ) 1, (ENNReal.ofReal (1 / y ^ 2)).toReal • (H ∘ ptXY) (x, y) =
        (∫ x in (0 : ℝ)..1, H (ofComplex (x + y * Complex.I))) / (y : ℂ) ^ 2 := by
      intro y
      rw [integral_smul, ENNReal.toReal_ofReal (by positivity), intervalIntegral.integral_of_le zero_le_one,
        integral_Ico_eq_integral_Ioc, Complex.real_smul]
      simp only [Function.comp_apply, ptXY]
      push_cast
      ring
    refine (integral_prod_symm _ hI).trans ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => key y)

end GlobalTheory.EisM

end
