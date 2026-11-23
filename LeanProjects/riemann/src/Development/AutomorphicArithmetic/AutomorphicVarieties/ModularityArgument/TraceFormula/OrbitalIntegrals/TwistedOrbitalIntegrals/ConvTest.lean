import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.convTest :
    UpperTheory.V.Z.Tf.Orb.ConvTest := by
  intro G _ _ _ _ _ _ _ _ μ hμ a b a1 a2 b1 b2
  constructor
  · have h : conv μ a b = fun x => ∫ y in tsupport a, a y * b (y⁻¹ * x) ∂μ := by
      funext x
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    rw [h]
    haveI : FirstCountableTopology G := inferInstance
    exact continuous_parametric_integral_of_continuous (by fun_prop) a2
  · refine HasCompactSupport.intro (a2.isCompact.mul b2.isCompact) fun x hx => ?_
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    by_contra hne
    exact hx ⟨y, subset_tsupport _ (left_ne_zero_of_mul hne), y⁻¹ * x, subset_tsupport _ (right_ne_zero_of_mul hne), by simp⟩
