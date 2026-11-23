import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrablePowerNormCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharMulVecArtinianReduced
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfSS
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.HeightDict

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem secondCountable_Fv' (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable
  haveI : TopologicalSpace.SeparableSpace (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) :=
    ⟨⟨Set.range (algebraMap F (v.adicCompletion F)), Set.countable_range _,
      HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
  infer_instance

private theorem secondCountable_Fv_tensor (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) := by
  classical
  haveI := secondCountable_Fv' (F := F) v
  let K := HeckeCharacterZeroLocus.SiegelWeilU.Fv F v
  let b := Module.Free.chooseBasis K (K ⊗[F] E)
  let e := b.equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : (K ⊗[F] E) ≃ₜ (Module.Free.ChooseBasisIndex K (K ⊗[F] E) → K) := ⟨e.toEquiv, h1, h2⟩
  exact h.secondCountableTopology

theorem vol_image_mulVec (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (μ : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    [μ.IsAddHaarMeasure] (M : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (L : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) :
    μ ((fun y => M.1 *ᵥ y) '' L) =
      ((GlobalTheory.Doubling.absEv F E v (Matrix.GeneralLinearGroup.det M) : ℝ≥0) : ℝ≥0∞) * μ L := by
  classical
  let K := HeckeCharacterZeroLocus.SiegelWeilU.Fv F v
  let B := K ⊗[F] E
  haveI : SecondCountableTopology K := secondCountable_Fv' v
  haveI : SecondCountableTopology B := secondCountable_Fv_tensor v
  haveI : BorelSpace K := ⟨rfl⟩
  haveI : TopologicalSpace.PseudoMetrizableSpace (Fin n → B) := inferInstance
  haveI : SigmaCompactSpace (Fin n → B) := inferInstance
  haveI : IsLocallyFiniteMeasure μ := inferInstance
  let V := Fin n → B
  let f : V →ₗ[K] V := (Matrix.mulVecLin M.1).restrictScalars K
  let b := Module.Free.chooseBasis K V
  let N := LinearMap.toMatrix b b f
  have hdet : N.det = Algebra.norm K M.1.det := by
    rw [LinearMap.det_toMatrix, LinearMap.det_restrictScalars]
    congr 1
    exact LinearMap.det_toLin' _
  have hM : IsUnit M.1.det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det M).isUnit
  have hu : IsUnit N.det := by
    rw [hdet]
    exact hM.map (Algebra.norm K)
  let e0 := b.equivFun
  have c1 : Continuous e0 := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
  have c2 : Continuous e0.symm := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap
  let e : (Module.Free.ChooseBasisIndex K V → K) ≃ₜ+ V :=
    { e0.symm.toAddEquiv with continuous_toFun := c2, continuous_invFun := c1 }
  let ψ : V ≃ₜ+ V := (e.symm.trans (GlobalTheory.ModuLR.mulVecCE N hu)).trans e
  have hψ : ∀ y, ψ y = M.1 *ᵥ y := by
    intro y
    show e0.symm (N *ᵥ e0 y) = M.1 *ᵥ y
    apply e0.injective
    rw [LinearEquiv.apply_symm_apply]
    exact LinearMap.toMatrix_mulVec_repr b b f y
  have hchar : addEquivAddHaarChar ψ = ‖Algebra.norm K M.1.det‖₊ := by
    rw [GlobalTheory.ModuLR.addEquivAddHaarChar_transport,
      GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE K inferInstance inferInstance _ N hu, ← hdet]
    have h1 := GlobalTheory.GaugeEx.modu_units K hu.unit
    rw [IsUnit.unit_spec] at h1
    rw [h1, ← GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v N.det hu.ne_zero]
    congr 1
    exact Units.ext rfl
  have key := MeasureTheory.addEquivAddHaarChar_smul_map μ ψ
  have himg : (fun y => M.1 *ᵥ y) '' L = ψ '' L := by
    congr 1
    funext y
    exact (hψ y).symm
  have hmap : (μ.map ψ) (ψ '' L) = μ L := by
    rw [show (ψ : V → V) = ψ.toHomeomorph.toMeasurableEquiv from rfl, MeasurableEquiv.map_apply]
    exact congrArg μ (Set.preimage_image_eq L ψ.injective)
  rw [himg, GlobalTheory.Doubling.absEv_apply, Matrix.GeneralLinearGroup.val_det_apply, ← hchar]
  conv_lhs => rw [← key]
  rw [Measure.smul_apply, hmap, ENNReal.smul_def, smul_eq_mul]

theorem vol_image_mulVec' (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (μ : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    [μ.IsAddHaarMeasure] (M : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (hM : IsUnit M.det)
    (L : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) :
    μ ((fun y => M *ᵥ y) '' L) = ((‖Algebra.norm (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) M.det‖₊ : ℝ≥0) : ℝ≥0∞) * μ L := by
  have h := vol_image_mulVec v μ (Matrix.nonsingInvUnit M hM) L
  rw [GlobalTheory.Doubling.absEv_apply] at h
  exact h

theorem exists_haar_tup (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ∃ lv : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E), lv.IsAddHaarMeasure := by
  haveI : SecondCountableTopology (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) := secondCountable_Fv_tensor (E := E) v
  exact ⟨Measure.addHaar, inferInstance⟩

end PositivityTheory.SiegelWeilFormula.HeightDict
