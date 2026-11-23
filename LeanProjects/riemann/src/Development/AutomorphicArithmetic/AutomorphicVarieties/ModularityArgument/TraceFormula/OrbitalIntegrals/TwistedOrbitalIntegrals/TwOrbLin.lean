import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.twOrbLin :
    UpperTheory.V.Z.Tf.Orb.TwOrbFin → UpperTheory.V.Z.Tf.Orb.TwOrbLin := by
  intro hT k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ hσ n _ _ μE hμE δ hδ μ hμ
  refine ⟨fun c φ => ?_, fun φ ψ a1 a2 b1 b2 => ?_⟩
  · simp only [twOrbIntegralC, quotIntegral]
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul _ _
    · simp
  · obtain ⟨h, p, -⟩ := hT k E σ hσ n μE hμE φ a1 a2 δ hδ μ hμ
    obtain ⟨-, q, -⟩ := hT k E σ hσ n μE hμE ψ b1 b2 δ hδ μ hμ
    simp only [twOrbIntegralC, quotIntegral, dif_pos h, Pi.add_apply, add_mul]
    exact integral_add (p _ h.choose_spec) (q _ h.choose_spec)
