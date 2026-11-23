import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

private lemma strip_meas : MeasurableSet strip := by
  have hre : Continuous fun z : ℍ => z.re := Complex.continuous_re.comp UpperHalfPlane.continuous_coe
  exact (measurableSet_le measurable_const hre.measurable).inter
    (measurableSet_lt hre.measurable measurable_const)

private lemma pt_re (x y : ℝ) (hy : 0 < y) : (pt x y).re = x := by
  rw [pt, ← UpperHalfPlane.coe_re, UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
  simp

private lemma vol_strip (hV : VolMap) :
    (volume : Measure ℍ).restrict strip = Measure.map (fun p : ℝ × ℝ => pt p.1 p.2)
      ((((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))).withDensity
        fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  obtain ⟨hm, hv⟩ := hV
  have hS := hm strip_meas
  have h1 : ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ioi 0) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have h2 : (fun p : ℝ × ℝ => pt p.1 p.2) ⁻¹' strip ∩ univ ×ˢ Ioi 0 = Ico 0 1 ×ˢ Ioi 0 := by
    ext ⟨x, y⟩
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioi, mem_Ico, strip,
      mem_setOf_eq]
    constructor
    · rintro ⟨h, hy⟩
      rw [pt_re x y hy] at h
      exact ⟨h, hy⟩
    · rintro ⟨h, hy⟩
      rw [pt_re x y hy]
      exact ⟨h, hy⟩
  rw [hv, Measure.restrict_map hm strip_meas, restrict_withDensity hS, h1,
    Measure.restrict_restrict hS, h2, Measure.prod_restrict]

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.stripFub :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.StripFub := by
  intro hV H hH
  have hf : Measurable fun p : ℝ × ℝ => pt p.1 p.2 := hV.1
  have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2) := by fun_prop
  have hlt : ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))),
      ENNReal.ofReal (1 / p.2 ^ 2) < ⊤ := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hμ := vol_strip hV
  have hI : Integrable H ((volume : Measure ℍ).restrict strip) := hH
  rw [hμ] at hI
  have hHm := hI.1
  rw [integrable_map_measure hHm hf.aemeasurable,
    integrable_withDensity_iff_integrable_smul' hg hlt] at hI
  have hpt : ∀ p : ℝ × ℝ, (ENNReal.ofReal (1 / p.2 ^ 2)).toReal • (H ∘ fun p : ℝ × ℝ => pt p.1 p.2) p
      = ((1 / p.2 ^ 2 : ℝ) : ℂ) * H (pt p.1 p.2) := by
    intro p
    rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    rfl
  have hF : Integrable (fun p : ℝ × ℝ => ((1 / p.2 ^ 2 : ℝ) : ℂ) * H (pt p.1 p.2))
      (((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))) :=
    hI.congr (Filter.Eventually.of_forall hpt)
  have hinner : ∀ y : ℝ, ∫ x, ((1 / y ^ 2 : ℝ) : ℂ) * H (pt x y) ∂(volume.restrict (Ico (0:ℝ) 1))
      = (∫ x in (0:ℝ)..1, H (pt x y)) / ((y ^ 2 : ℝ) : ℂ) := by
    intro y
    rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
      integral_Ico_eq_integral_Ioc, one_div, Complex.ofReal_inv, div_eq_inv_mul]
  refine ⟨?_, ?_⟩
  · have := hF.integral_prod_right
    simp only [hinner] at this
    exact this
  · calc ∫ z in strip, H z
        = ∫ p, H (pt p.1 p.2) ∂((((volume : Measure ℝ).restrict (Ico 0 1)).prod
            (volume.restrict (Ioi 0))).withDensity fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
          rw [hμ, integral_map hf.aemeasurable hHm]
      _ = ∫ p, ((1 / p.2 ^ 2 : ℝ) : ℂ) * H (pt p.1 p.2) ∂(((volume : Measure ℝ).restrict (Ico 0 1)).prod
            (volume.restrict (Ioi 0))) := by
          rw [integral_withDensity_eq_integral_toReal_smul hg hlt]
          exact integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ∫ y in Ioi 0, ∫ x, ((1 / y ^ 2 : ℝ) : ℂ) * H (pt x y) ∂(volume.restrict (Ico (0:ℝ) 1)) :=
          integral_prod_symm _ hF
      _ = _ := by simp only [hinner]
