import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertOfUnramifiedIsometricInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertDatumOfInvolutionUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterOfUnramifiedInertDefiniteUnStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertSatakeHeckeEigenvaluesAlgebraicAutomorphicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterNeZeroOfSameTransformStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertDict

theorem satake_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → (π.SphAt v → IsUnramU U w) ∧ ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → (∃ Dv : InertDatum L n v w, Dv.σw = s ∧ Dv.ϖ = ϖ) ∧ ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), Dv.σw = s → Dv.ϖ = ϖ → NG.SatAt π Dv α → ∃ α' : Fin (n / 2) → ℂˣ, (∀ i, (α' i : ℂ) = α i) ∧ HasSatAt U w s ϖ q α' := by
  intro L _ _ _ n F π U hD v w hO
  refine ⟨GlobalTheory.T.isUnramified_of_sphericalVector_dictionary L n F π U hD v w hO, fun s ϖ q hs hU => ?_⟩
  obtain ⟨hun, hns, hq⟩ := GlobalTheory.T.inert_of_unramifiedIsometricInvolution L v w hO s ϖ q hs hU
  refine ⟨GlobalTheory.T.exists_inertDatum_of_involution_uniformizer L n v w hO hun hns s ϖ hs (hq ▸ hU), fun Dv α hσ hϖ hsat => ?_⟩
  have hsph : π.SphAt v := by
    obtain ⟨f, hf, hf0, U0, hU0, hU0', -⟩ := hsat
    exact ⟨f, hf, hf0, fun κ hκ ht => hU0 κ ((hU0' κ ht).2 hκ)⟩
  obtain ⟨α0, h0⟩ := GlobalTheory.T.exists_satakeParameter_of_unramified_inert_definiteUnitary L n U hD.1 w hun hns s ϖ q hs hU (GlobalTheory.T.isUnramified_of_sphericalVector_dictionary L n F π U hD v w hO hsph)
  subst hσ hϖ hq
  have heq := GlobalTheory.T.inertSatake_heckeEigenvalues_algebraic_automorphic L n F π U hD v w hO Dv α hsat α0 h0
  have hnz := GlobalTheory.T.satakeParameter_ne_zero_of_sameTransform (w.adicCompletion L) Dv.ϖ Dv.σw _ n hU α α0 heq
  refine ⟨fun i => Units.mk0 (α i) (hnz i), fun i => rfl, ?_⟩
  obtain ⟨b, hb, hb2, p, hp, σ, hc, hs1, hs2⟩ := h0
  refine ⟨b, hb, hb2, p, hp, σ, hc, hs1, fun x hx hx0 => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hs2 x hx hx0
  refine ⟨a1, a2, fun h hh => ?_⟩
  rw [a3 h hh, ← heq h hh]
  rfl

end GlobalTheory.InertDict
