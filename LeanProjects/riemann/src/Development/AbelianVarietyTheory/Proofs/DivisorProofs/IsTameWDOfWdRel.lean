import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTheRecOfIsRecLit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TameTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω']
  {A' : ValuationSubring Ω'} {φ : Ω ≃+* Ω'}

theorem val_lt_val_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) (a b : Ω) (hb : b ≠ 0) :
    A'.valuation (φ a) < A'.valuation (φ b) ↔ A.valuation a < A.valuation b := by
  have hb' : φ b ≠ 0 := (map_ne_zero φ).mpr hb
  have h1 : A'.valuation (φ b) ≠ 0 := by simpa using hb'
  have h2 : A.valuation b ≠ 0 := by simpa using hb
  have e1 : A'.valuation (φ a) < A'.valuation (φ b) ↔ A'.valuation (φ (a / b)) < 1 := by
    rw [map_div₀, map_div₀, div_lt_one₀ (zero_lt_iff.mpr h1)]
  have e2 : A.valuation a < A.valuation b ↔ A.valuation (a / b) < 1 := by
    rw [map_div₀, div_lt_one₀ (zero_lt_iff.mpr h2)]
  rw [e1, e2, GlobalTheory.WeilTransport.val_lt_one_iff hm]

theorem isWild_of_rel (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) {σ : G E Ω} {σ' : G E' Ω'}
    (hrel : ∀ z, φ (σ z) = σ' (φ z)) (hσ : Formalism.MainNotions.BlochKatoReduction.IsWild A σ) : Formalism.MainNotions.BlochKatoReduction.IsWild A' σ' := by
  obtain ⟨⟨hdec, hin⟩, hw⟩ := hσ
  refine ⟨⟨(GlobalTheory.WeilTransport.mem_Dec_iff hm hrel).mpr hdec, fun x hx => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := φ.surjective x
    rw [GlobalTheory.WeilTransport.val_le_one_iff hm] at hx
    rw [← hrel, ← map_sub, GlobalTheory.WeilTransport.val_lt_one_iff hm]
    exact hin z hx
  · obtain ⟨z, rfl⟩ := φ.surjective x
    have hz : z ≠ 0 := by rintro rfl; exact hx (map_zero φ)
    rw [← hrel, ← map_sub, val_lt_val_iff hm _ _ hz]
    exact hw z hz

end GlobalTheory.TameTransport
