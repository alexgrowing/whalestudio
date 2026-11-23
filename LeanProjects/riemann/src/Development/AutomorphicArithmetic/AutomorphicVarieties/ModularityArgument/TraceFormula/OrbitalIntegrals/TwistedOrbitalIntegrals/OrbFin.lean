import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.orbFin :
    UpperTheory.V.Z.Tf.Orb.TwOrbFin → UpperTheory.V.Z.Tf.Orb.Untwist → UpperTheory.V.Z.Tf.Orb.OrbFin := by
  intro hT hU k _ _ _ _ _ n _ _ μk hμk f hf hc γ hγ μ hμ
  haveI : ValuativeExtension k k := ⟨fun _ _ => Iff.rfl⟩
  obtain ⟨h0, h1, h2, h3⟩ := hU k n μk γ
  obtain ⟨μ', a, b, c⟩ := h3 μ hμ
  obtain ⟨⟨ρ, hρ⟩, t2, t3⟩ := hT k k 1 h0 n μk hμk f hf hc γ (h2 hγ) μ' a
  simp only [twConj, h1] at t2 t3
  exact ⟨⟨ρ, (b ρ).1 hρ⟩, fun ρ h => t2 ρ ((b ρ).2 h), fun p q => c f ▸ t3 p q⟩
