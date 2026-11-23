import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_isCompact_open_preimage_eq_of_isInducing {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PrespectralSpace Y] {f : X → Y} (hf : Topology.IsInducing f) {U : Set X} (hU : IsOpen U) (hc : IsCompact U) :
    ∃ V : Set Y, IsOpen V ∧ IsCompact V ∧ f ⁻¹' V = U := by
  obtain ⟨W, hW, rfl⟩ := hf.isOpen_iff.1 hU
  obtain ⟨V, hVc, hVo, h1, h2⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
    (hc.image hf.continuous) hW (Set.image_preimage_subset _ _)
  exact ⟨V, hVo, hVc, Set.Subset.antisymm (Set.preimage_mono h2) (Set.image_subset_iff.1 h1)⟩

theorem exists_isCompact_open_preimage_eq_baseChange_atPrime : ∀ (R : Type) [CommRing R] (q : PrimeSpectrum R) (T : Scheme.{0}) (π : T ⟶ Sp R) (U' : (pullback π (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))).Opens), IsCompact (U' : Set (pullback π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) : Scheme.{0})) → ∃ U₀ : T.Opens, IsCompact (U₀ : Set T) ∧ pullback.fst π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) ⁻¹ᵁ U₀ = U' := by
  intro R _ q T π U' hU'
  have h₀ : IsPreimmersion (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) :=
    IsPreimmersion.of_isLocalization q.asIdeal.primeCompl
  have : IsPreimmersion (pullback.fst π (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip h₀
  obtain ⟨V, hVo, hVc, h⟩ := exists_isCompact_open_preimage_eq_of_isInducing
    (pullback.fst π (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))).isEmbedding.isInducing U'.isOpen hU'
  exact ⟨⟨V, hVo⟩, hVc, TopologicalSpace.Opens.ext h⟩

end GlobalTheory
