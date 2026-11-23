import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.twCent :
    UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.TwCent := by
  intro hE hG hC k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ _ n δ hδ
  have := (hG E n).2.2.1
  have hc := ((hE k E).2.2 n).2 σ
  have hp : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  refine ⟨isClosed_eq (f := fun g : GL (Fin n) E => g⁻¹ * δ * sigmaGL σ g) ((continuous_inv.mul continuous_const).mul hc)
    continuous_const, fun a ha b hb => ?_⟩
  have h1 := congrArg Units.val (twCent_commute_twNorm _ hp δ ha)
  have h2 := congrArg Units.val (twCent_commute_twNorm _ hp δ hb)
  exact Units.ext (hC E n _ a.val b.val hδ h1 h2)
