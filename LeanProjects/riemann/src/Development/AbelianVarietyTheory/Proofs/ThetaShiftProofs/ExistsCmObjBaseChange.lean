import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmExistsOnOfPointCarriesObject

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem exists_cmObj_baseChange : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (K₂ : Type) [Field K₂] [NumberField K₂] (i : K →+* K₂) (σ₂ : K₂ →+* ℂ), σ₂.comp i = σ₁ → ∃ (ρ₂ : 𝓞 K₂) (X₂ : GlobalTheory.CM.CMObj H K₂ ρ₂ σ₂ p q) (_ : SABMap X₂.B.t X.B.t (spMap (RingOfIntegers.mapRingHom i))), (ρ₂ : K₂) = i (ρ : K) ∧ X₂.hh = X.hh := by
  intro _ E _ _ _ H K _ _ ρ σ₁ p q X K₂ _ _ i σ₂ h
  obtain ⟨X₂, -, mb, hh, -⟩ := GlobalTheory.CMExistsCompare.exists_cmObj_extend X i σ₂ h
  exact ⟨_, X₂, mb, rfl, hh⟩

end GlobalTheory.ArcCM
