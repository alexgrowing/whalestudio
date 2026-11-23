import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.UnlAway
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeMatchBaseChange
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.GalN UpperTheory.GalN.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.GalN.V.L.unlres :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A w → IsPlaceOver A v → UnlAt ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) v A → UnlAt ι r w A := by
  intro F Ω _ _ _ _ _ l _ ι n r w A K _ _ _ _ _ v hw hv h
  obtain ⟨s, j, hj, ⟨hdec, hres⟩, hroot⟩ := h
  have hu : v.under (𝓞 F) = w := by
    have h1 : IsPlaceOver A (v.under (𝓞 F)) := GlobalTheory.AboveL.SatBC.isPlaceOver_under hv
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    exact (h1 x).symm.trans (hw x)
  have hN : normV v = normV w ^ v.asIdeal.inertiaDeg (𝓞 F) := by
    have := GlobalTheory.AboveL.SatBC.normV_under_pow F K v
    rwa [hu] at this
  have hf : 1 ≤ v.asIdeal.inertiaDeg (𝓞 F) := by
    rcases Nat.eq_zero_or_pos (v.asIdeal.inertiaDeg (𝓞 F)) with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hN
      have hne : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
      exact hne (Ideal.absNorm_eq_one_iff.1 hN)
    · exact h0
  set f := v.asIdeal.inertiaDeg (𝓞 F) with hfdef
  have hpow : normV v ^ j = normV w ^ (f * j) := by rw [hN, pow_mul]
  refine ⟨s.restrictScalars F, f * j, Nat.mul_pos hf hj, ⟨?_, ?_⟩, ?_⟩
  · exact hdec
  · intro x hx
    have := hres x hx
    rw [hpow] at this
    exact this
  · intro α hα hα'
    have e : ((normV v : ℕ) : ℂ) ^ j = ((normV w : ℕ) : ℂ) ^ (f * j) := by exact_mod_cast hpow
    refine hroot α hα ?_
    rw [e]
    exact hα'
