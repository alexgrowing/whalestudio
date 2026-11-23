import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
import GroundTheory.LocalFields.Unramified
import GroundTheory.AutomorphicForms.Measures

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.unimod :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.Unimod := by
  intro hG E _ _ _ _ n _ _ μ hμ
  obtain ⟨h1, h2, h3, ⟨K, hKo, hKc⟩, -⟩ := hG E n
  have hr := GroundTheory.Automorphic.Measures.isMulRightInvariant_GL E n μ
  refine ⟨hr, ⟨?_⟩⟩
  have : IsFiniteMeasureOnCompacts μ.inv := ⟨fun C hC => by
    rw [Measure.inv_apply]
    exact hC.inv.measure_lt_top⟩
  have e := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h4 := congrArg (fun ν : Measure (GL (Fin n) E) => ν K) e
  have h0 : μ K ≠ 0 := hKo.measure_ne_zero μ ⟨1, K.one_mem⟩
  have ht : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  simp only [Measure.inv_apply, inv_coe_set, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h4
  have h5 : ((μ.inv.haarScalarFactor μ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 (by rw [one_mul]; exact h4.symm)
  rw [e, ENNReal.coe_eq_one.1 h5, one_smul]
