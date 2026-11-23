import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
import GroundTheory.LocalFields.Unramified
import GroundTheory.LocalFields.UnramifiedGalois

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.extCont :
    UpperTheory.V.Z.Tf.Orb.ExtCont := by
  intro k _ _ _ _ E _ _ _ _ _ _ _
  let _ := GroundTheory.LocalField.nontriviallyNormedField k
  have := GroundTheory.LocalField.completeSpace_nontriviallyNormedField k
  have := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField E
  have h1 : Continuous (algebraMap k E) := (Algebra.linearMap k E).continuous_of_finiteDimensional
  have h2 : ∀ σ : E ≃ₐ[k] E, Continuous σ := fun σ => σ.toLinearMap.continuous_of_finiteDimensional
  refine ⟨h1, h2, fun n => ⟨?_, fun σ => ?_⟩⟩
  · exact Continuous.units_map ((algebraMap k E).mapMatrix (m := Fin n)).toMonoidHom (continuous_id.matrix_map h1)
  · exact Continuous.units_map ((σ.toAlgHom.toRingHom).mapMatrix (m := Fin n)).toMonoidHom (continuous_id.matrix_map (h2 σ))
