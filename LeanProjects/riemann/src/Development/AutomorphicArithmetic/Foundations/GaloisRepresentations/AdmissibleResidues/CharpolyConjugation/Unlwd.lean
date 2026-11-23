import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.UnlAway
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.GalN UpperTheory.GalN.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.GalN.V.L.unlwd :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal), Continuous r → UnlAt ι r w A → ∃ g : ↥(Weil h), NoRatio (wdOf h hl ι r) g := by
  intro F Ω _ _ _ _ _ l _ ι n r w A h hl hr hu
  obtain ⟨s, j, _, hs, hno⟩ := hu
  have ha : ActsAs A (normV w) s j 0 := by
    have h1 := actsAs_one_iff.mpr hs
    refine ⟨h1.1, fun x hx => ?_⟩
    simpa using h1.2 x hx
  have hc : Continuous fun g => (r g : Matrix (Fin n) (Fin n) (Qbar l)) :=
    Units.continuous_val.comp hr
  have hd : deg (⟨s, j, 0, ha⟩ : Weil h) = j := by
    simpa using deg_eq (σ := (⟨s, j, 0, ha⟩ : Weil h)) ha
  refine ⟨⟨s, j, 0, ha⟩, ?_⟩
  intro α hα hβ
  rw [WD.eig, charPol_wdOf hl ι hc] at hα hβ
  rw [hd, zpow_natCast] at hβ
  exact hno α (isRoot_of_mem_roots hα) (isRoot_of_mem_roots hβ)
