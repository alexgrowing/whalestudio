import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal NNReal

noncomputable section

namespace PositivityTheory.Rg.BcB.CV.QuotientMapAlt

def subEquiv {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (e : G ≃ₜ* G') (T : Subgroup G) : T ≃ₜ* T.map e.toMonoidHom where
  toFun t := ⟨e t, Subgroup.mem_map.2 ⟨t, t.2, rfl⟩⟩
  invFun t := ⟨e.symm t, by
    obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.1 t.2
    have h : e.symm (t : G') = s := by
      rw [← hst]
      exact e.symm_apply_apply s
    rw [h]
    exact hs⟩
  left_inv t := Subtype.ext (e.symm_apply_apply (t : G))
  right_inv t := Subtype.ext (e.apply_symm_apply (t : G'))
  map_mul' s t := Subtype.ext (map_mul e (s : G) (t : G))
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

end PositivityTheory.Rg.BcB.CV.QuotientMapAlt

open PositivityTheory.Rg.BcB.CV.QuotientMapAlt in
theorem PositivityTheory.Rg.BcB.CV.pf_QMap : PositivityTheory.Rg.BcB.D4.NormEq → PositivityTheory.Rg.BcB.CV.QMap := by
  intro hN G _ _ _ _ _ _ _ _ G' _ _ _ _ _ _ _ _ e μ _ μ' _ T T' ν _ _ ν' _ _ F hTc hT hF hFT h0
  subst hT
  have hT'c : IsClosed ((T.map e.toMonoidHom : Subgroup G') : Set G') := by
    rw [Subgroup.coe_map]
    exact e.toHomeomorph.isClosedMap _ hTc
  have : SecondCountableTopology T := inferInstanceAs (SecondCountableTopology (T : Set G))
  have : SecondCountableTopology (T.map e.toMonoidHom) :=
    inferInstanceAs (SecondCountableTopology ((T.map e.toMonoidHom : Subgroup G') : Set G'))
  have : LocallyCompactSpace T := hTc.locallyCompactSpace
  have : LocallyCompactSpace (T.map e.toMonoidHom) := hT'c.locallyCompactSpace
  by_cases hex : ∃ ρ, IsQuotNormaliser T ν ρ
  swap
  · rw [quotIntegral, dif_neg hex]
  rw [quotIntegral, dif_pos hex]
  have hρ : IsQuotNormaliser T ν hex.choose := hex.choose_spec
  set ρ := hex.choose

  let φ := subEquiv e T
  let c : ℝ≥0 := Measure.haarScalarFactor (Measure.map φ.symm ν') ν
  have hc : Measure.map φ.symm ν' = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : (0 : ℝ≥0) < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hcne : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0.ne'
  let ρ' : G' → ℝ≥0∞ := fun x => (c : ℝ≥0∞)⁻¹ * ρ (e.symm x)
  have hρ' : IsQuotNormaliser (T.map e.toMonoidHom) ν' ρ' := by
    refine ⟨measurable_const.mul (hρ.1.comp e.symm.continuous.measurable), fun x => ?_⟩
    have hk : Measurable fun t : T => ρ ((t : G) * e.symm x) :=
      hρ.1.comp (measurable_subtype_coe.mul_const _)
    have h1 : ∫⁻ h : T.map e.toMonoidHom, ρ' ((h : G') * x) ∂ν' =
        (c : ℝ≥0∞)⁻¹ * ∫⁻ t, ρ ((t : G) * e.symm x) ∂(Measure.map φ.symm ν') := by
      rw [lintegral_map hk (show Measurable (⇑φ.symm) from φ.symm.continuous.measurable),
        ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hcne)]
      refine lintegral_congr fun h => ?_
      show (c : ℝ≥0∞)⁻¹ * ρ (e.symm ((h : G') * x)) = _
      rw [map_mul]
      rfl
    rw [h1, hc, lintegral_smul_measure, hρ.2, ENNReal.smul_def, smul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel hcne ENNReal.coe_ne_top

  let eM : G' ≃ᵐ G := e.symm.toHomeomorph.toMeasurableEquiv
  have hH : (Measure.map eM μ').IsHaarMeasure :=
    (inferInstance : (Measure.map e.symm μ').IsHaarMeasure)
  let a : ℝ≥0 := Measure.haarScalarFactor (Measure.map eM μ') μ
  have ha : Measure.map eM μ' = a • μ := Measure.isMulLeftInvariant_eq_smul _ _
  have ha0 : (0 : ℝ≥0) < a := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hF' : Measurable fun x => F (e.symm x) := hF.comp e.symm.continuous.measurable
  have hFT' : ∀ h ∈ T.map e.toMonoidHom, ∀ x, F (e.symm (h * x)) = F (e.symm x) := by
    intro h hh x
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hh
    show F (e.symm (e t * x)) = _
    rw [map_mul, e.symm_apply_apply]
    exact hFT t ht _
  have hex' : ∃ ρ, IsQuotNormaliser (T.map e.toMonoidHom) ν' ρ := ⟨ρ', hρ'⟩
  rw [quotIntegral, dif_pos hex', hN G' μ' _ ν' _ _ ρ' hF' hFT' hex'.choose_spec hρ'] at h0
  have key : a • ∫ g, F g * ((((c : ℝ≥0∞)⁻¹ * ρ g).toReal : ℝ) : ℂ) ∂μ = 0 := by
    rw [← integral_smul_nnreal_measure, ← ha, integral_map_equiv]
    exact h0
  have key2 : ∫ g, F g * ((((c : ℝ≥0∞)⁻¹ * ρ g).toReal : ℝ) : ℂ) ∂μ = 0 := by
    have := congrArg (fun z : ℂ => (a⁻¹ : ℝ≥0) • z) key
    simpa [smul_smul, inv_mul_cancel₀ ha0.ne'] using this
  have hcr : ((c : ℝ≥0∞)⁻¹).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top, ENNReal.inv_ne_top.2 hcne⟩
  have key3 : ∫ g, F g * ((((c : ℝ≥0∞)⁻¹ * ρ g).toReal : ℝ) : ℂ) ∂μ =
      (((c : ℝ≥0∞)⁻¹).toReal : ℂ) * ∫ g, F g * (((ρ g).toReal : ℝ) : ℂ) ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [ENNReal.toReal_mul, Complex.ofReal_mul]
    ring
  rw [key3] at key2
  exact (mul_eq_zero.1 key2).resolve_left (by exact_mod_cast hcr)
