import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory PositivityTheory.Rg.Tf.Loc in
theorem UpperTheory.V.Z.Tf.Orb.quotScale :
    UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotScale := by
  intro hI G _ _ _ _ _ _ _ _ μG hμG H μ hs hinv c hc F hF hFH
  have hc0 : (c : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hc
  have hct : (c : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsm : (c • μ : Measure H) = (c : ENNReal) • μ := rfl
  by_cases hex : ∃ ρ, IsQuotNormaliser H μ ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hρ' : IsQuotNormaliser H (c • μ) (fun g => (c : ENNReal)⁻¹ * ρ g) := by
      refine ⟨hρ.1.const_mul _, fun g => ?_⟩
      rw [hsm, lintegral_smul_measure,
        lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hc0), hρ.2 g, mul_one, smul_eq_mul,
        ENNReal.mul_inv_cancel hc0 hct]
    have hs' : SFinite (c • μ) := by rw [hsm]; infer_instance
    have hinv' : (c • μ).IsInvInvariant := by
      constructor
      have h1 : μ.inv = μ := Measure.inv_eq_self μ
      rw [Measure.inv] at h1 ⊢
      rw [hsm, Measure.map_smul, h1]
    rw [hI G μG hμG H μ hs hinv F hF hFH ρ hρ,
      hI G μG hμG H (c • μ) hs' hinv' F hF hFH _ hρ', ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.coe_toReal]
    push_cast
    ring
  · have hex' : ¬ ∃ ρ, IsQuotNormaliser H (c • μ) ρ := by
      rintro ⟨ρ, hρ⟩
      refine hex ⟨fun g => (c : ENNReal) * ρ g, hρ.1.const_mul _, fun g => ?_⟩
      have h2 := hρ.2 g
      rw [hsm, lintegral_smul_measure, smul_eq_mul] at h2
      rw [lintegral_const_mul' _ _ hct, h2]
    simp only [quotIntegral, dif_neg hex, dif_neg hex', mul_zero]
