import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodAUIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatakeParameterSphericalInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatakeParameterAtInertPlaceOfSphericalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterInertDatumOfDictionarySpherStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertSatakeParametersAgreeUnderDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalReciprocityUnramifiedSpherical

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M.Sph

theorem exists_satAt_of_sphAtG : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ Dv : InertDatum L n v w, SphAtG π v → ∃ α, NG.SatAt π Dv α :=
  fun L _ _ _ n π v w h Dv hs => GlobalTheory.T.exists_satakeParameter_spherical_inertPlace L n π v w h Dv hs.1

theorem exists_satAt_of_overPl_sphAtG : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → SphAtG π v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α :=
  fun L _ _ _ n π v w h hs => GlobalTheory.T.exists_satakeParameter_at_inertPlace_of_spherical L n π v w h hs.1

theorem exists_satAt_of_dict : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → SphAtG π v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α :=
  fun L _ _ _ n F π U hD v w h hs => GlobalTheory.T.exists_satakeParameter_inertDatum_of_dictionary_spherical L n F π U hD v w h hs.1

theorem satAgree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → (SphAtG π v → IsUnramU U w) ∧ ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → (∃ Dv : InertDatum L n v w, Dv.σw = s ∧ Dv.ϖ = ϖ) ∧ ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), Dv.σw = s → Dv.ϖ = ϖ → NG.SatAt π Dv α → ∃ α' : Fin (n / 2) → ℂˣ, (∀ i, (α' i : ℂ) = α i) ∧ HasSatAt U w s ϖ q α' :=
  fun L _ _ _ n F π U hD v w h => ⟨fun hs => (GlobalTheory.T.inert_satake_parameters_agree_under_dictionary L n F π U hD v w h).1 hs.1, (GlobalTheory.T.inert_satake_parameters_agree_under_dictionary L n F π U hD v w h).2⟩

theorem isSph {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hσ : IsLocS π.S s σ) (hs : SphAtG π s.v) :
    GlobalTheory.SmGL.IsSpherical σ.ρ := GlobalTheory.SphLoc.isSpherical_of_sphAt π s σ hσ hs.1

end UpperTheory.One.M.Sph
