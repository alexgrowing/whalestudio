import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaFamilyPrescribedLeadingTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNonzeroAtOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaNormalisationConstantOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionScalarsRescaleStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_unit_normalisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F) → ∃ Φ' : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ' F) F := by
  intro R _ _ _ hR D C
  obtain ⟨k₁, hk₁⟩ := GlobalTheory.T.exists_weightZero_section_nonzero_at_origin R hR D
  refine ⟨max k₁ 1, fun k hk Φ hΦ => ?_⟩
  obtain ⟨b₀, hb₀⟩ := hk₁ k (le_of_max_le_left hk)
  have hk1 : 1 ≤ k := le_of_max_le_right hk
  obtain ⟨F₀, hF₀⟩ := (GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm R hR D).2 k hk1 b₀
  obtain ⟨c₁, c₂, hc₂, hc⟩ := GlobalTheory.T.exists_thetaNormalisationConstant_origin R hR D C k hk1 b₀ hb₀ F₀ hF₀ (Φ F₀)
  refine ⟨fun F => scal C.A.A.hom (algebraMap R (FractionRing R) c₁ / algebraMap R (FractionRing R) c₂) • Φ F,
    fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, ha, hb, hE⟩ := hΦ W T
  obtain ⟨u, hu⟩ := hc W T a b ha hb (hE F₀)
  exact ⟨u, fun F => GlobalTheory.T.trait_expansionScalars_rescale R hR D C W T k (Φ F) F a b u c₁ c₂ ha hc₂ hu (hE F)⟩

end GlobalTheory.Mum
