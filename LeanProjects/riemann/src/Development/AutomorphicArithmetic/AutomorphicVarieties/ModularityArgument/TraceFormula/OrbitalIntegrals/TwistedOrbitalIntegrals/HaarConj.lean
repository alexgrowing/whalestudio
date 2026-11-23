import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.haarConj :
    UpperTheory.V.Z.Tf.Orb.HaarConj := by
  intro G _ _ _ _ _ _ _ _ H H' y hy μ hμ
  let e : H ≃ₜ* H' :=
    { toFun := fun x => ⟨y⁻¹ * x * y, (hy x).1 x.2⟩
      invFun := fun z => ⟨y * z * y⁻¹, (hy _).2 (by simp [mul_assoc])⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨μ.map e, e.isHaarMeasure_map μ, ?_⟩
  have he : Measurable (e : H → H') := (map_continuous e).measurable
  exact (Measure.map_map (g := fun x : H' => (x : G)) measurable_subtype_coe he).symm
