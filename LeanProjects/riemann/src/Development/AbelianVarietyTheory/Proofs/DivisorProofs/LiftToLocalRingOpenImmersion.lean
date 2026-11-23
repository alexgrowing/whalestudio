import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

theorem GlobalTheory.openImmersion_factor_localization_atPrime : ∀ {X U : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] {A : Type} [CommRing A] (ξ : Sp A ⟶ X)
    (𝔭 : PrimeSpectrum A), ξ 𝔭 ∈ Set.range j →
    ∃ y : Sp (Localization.AtPrime 𝔭.asIdeal) ⟶ U, y ≫ j = spMap (algebraMap A _) ≫ ξ := by
  intro X U j _ A _ ξ 𝔭 h𝔭
  have hopen : IsOpen (Set.range j) := j.isOpenEmbedding.isOpen_range
  have hsub : Set.range (spMap (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) ≫ ξ) ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    have hx : x ⤳ IsLocalRing.closedPoint (Localization.AtPrime 𝔭.asIdeal) :=
      IsLocalRing.specializes_closedPoint x
    have h2 := hx.map (spMap (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) ≫ ξ).continuous
    refine h2.mem_open hopen ?_
    have hc : (spMap (algebraMap A (Localization.AtPrime 𝔭.asIdeal))) (IsLocalRing.closedPoint (Localization.AtPrime 𝔭.asIdeal)) = 𝔭 := by
      apply PrimeSpectrum.ext
      exact Localization.AtPrime.under_maximalIdeal
    change ξ ((spMap (algebraMap A (Localization.AtPrime 𝔭.asIdeal))) (IsLocalRing.closedPoint (Localization.AtPrime 𝔭.asIdeal))) ∈ _
    rw [hc]; exact h𝔭
  exact ⟨IsOpenImmersion.lift j _ hsub, IsOpenImmersion.lift_fac _ _ _⟩
