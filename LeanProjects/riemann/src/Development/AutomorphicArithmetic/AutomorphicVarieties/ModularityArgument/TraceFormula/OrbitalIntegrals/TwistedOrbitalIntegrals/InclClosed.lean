import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport
import GroundTheory.LocalFields.Unramified
import GroundTheory.LocalFields.UnramifiedGalois

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.inclClosed :
    UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.InclClosed := by
  intro _ k E _ _ _ _ _ _ _ _ _ _ _ n
  let _ := GroundTheory.LocalField.nontriviallyNormedField k
  have := GroundTheory.LocalField.completeSpace_nontriviallyNormedField k
  have := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField E
  have h : Topology.IsClosedEmbedding (algebraMap k E) :=
    LinearMap.isClosedEmbedding_of_injective (f := Algebra.linearMap k E) (LinearMap.ker_eq_bot.mpr (algebraMap k E).injective)
  have hM : Topology.IsEmbedding
      ((algebraMap k E).mapMatrix.toMonoidHom : Matrix (Fin n) (Fin n) k →* Matrix (Fin n) (Fin n) E) :=
    Topology.IsEmbedding.piMap (f := fun _ : Fin n => Pi.map fun _ : Fin n => algebraMap k E)
      fun _ => Topology.IsEmbedding.piMap fun _ => h.isEmbedding
  refine ⟨hM.units_map, ?_⟩
  have e : Set.range (incl : GL (Fin n) k → GL (Fin n) E) =
      ⋂ i, ⋂ j, (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j) ⁻¹' Set.range (algebraMap k E) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · rintro ⟨y, rfl⟩ i j
      exact ⟨(y : Matrix (Fin n) (Fin n) k) i j, rfl⟩
    · intro h
      choose M hM using h
      have e : (algebraMap k E).mapMatrix (Matrix.of M) = (g : Matrix (Fin n) (Fin n) E) := by
        ext i j
        exact hM i j
      have hd : (Matrix.of M).det ≠ 0 := fun h0 => by
        have h1 := RingHom.map_det (algebraMap k E) (Matrix.of M)
        rw [h0, map_zero, e] at h1
        exact (Matrix.GeneralLinearGroup.det g).ne_zero h1.symm
      exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, Units.ext e⟩
  rw [e]
  exact isClosed_iInter fun i => isClosed_iInter fun j => h.isClosed_range.preimage (Units.continuous_val.matrix_elem i j)
