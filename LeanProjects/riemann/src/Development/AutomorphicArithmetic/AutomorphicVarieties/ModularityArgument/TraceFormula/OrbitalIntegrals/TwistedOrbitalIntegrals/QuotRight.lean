import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory PositivityTheory.Rg.Tf.Loc in
theorem UpperTheory.V.Z.Tf.Orb.quotRight :
    UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotRight := by
  intro hI G _ _ _ _ _ _ _ _ μG hμG hR H μ hs hinv F hF hFH y
  by_cases hex : ∃ ρ, IsQuotNormaliser H μ ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hρ' : IsQuotNormaliser H μ (fun g => ρ (g * y)) := by
      refine ⟨hρ.1.comp (measurable_mul_const y), fun g => ?_⟩
      simpa only [mul_assoc] using hρ.2 (g * y)
    rw [hI G μG hμG H μ hs hinv F hF hFH ρ hρ,
      hI G μG hμG H μ hs hinv (fun g => F (g * y)) (hF.comp (measurable_mul_const y))
        (fun h hh g => by rw [mul_assoc, hFH h hh]) _ hρ']
    exact integral_mul_right_eq_self (fun g => F g * ((ρ g).toReal : ℂ)) y
  · simp only [quotIntegral, dif_neg hex]
