import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.orbComm :
    UpperTheory.V.Z.Tf.Orb.TwOrbComm → UpperTheory.V.Z.Tf.Orb.Untwist → UpperTheory.V.Z.Tf.Orb.OrbComm := by
  intro hT hU k _ _ _ _ _ n _ _ μk hμk γ hγ μ hμ f f' p1 p2 p3 p4
  haveI : ValuativeExtension k k := ⟨fun _ _ => Iff.rfl⟩
  obtain ⟨h0, h1, h2, h3⟩ := hU k n μk γ
  obtain ⟨μ', a, b, c⟩ := h3 μ hμ
  have t := hT k k 1 h0 n μk hμk γ (h2 hγ) μ' a f f' p1 p2 p3 p4 fun x => by rw [h1]
  simpa only [c] using t
