import Mathlib
import GroundTheory.GlobalFields.LocalAtPlace
import GroundTheory.GlobalFields.Adele.Approximation
import GroundTheory.GlobalFields.Adele.Discrete

namespace GroundTheory.Global

open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

variable (K : Type*) [Field K] [NumberField K]

theorem isCompact_integralFiniteAdeles :
    IsCompact (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
  have : ∀ v : HeightOneSpectrum (𝓞 K),
      CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    isCompact_iff_compactSpace.1 (isCompact_adicCompletionIntegers v)
  have hcont := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (𝓕 := Filter.cofinite)).continuous
  have h := isCompact_range hcont
  rw [RestrictedProduct.range_structureMap] at h
  exact h

abbrev AdeleQuotient : Type _ := 𝔸[K] ⧸ AdeleRing.principalSubgroup (𝓞 K) K

instance : IsClosed (AdeleRing.principalSubgroup (𝓞 K) K : Set 𝔸[K]) :=
  isClosed_principalSubgroup K

instance compactSpace_adeleQuotient : CompactSpace (AdeleQuotient K) := by
  obtain ⟨C, hC, hx⟩ := exists_isCompact_forall_exists_sub_mem K
  have hD : IsCompact (C ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) :
      Set 𝔸[K]) := hC.prod (isCompact_integralFiniteAdeles K)
  refine ⟨?_⟩
  convert hD.image (QuotientAddGroup.continuous_mk (N := AdeleRing.principalSubgroup (𝓞 K) K))
  refine (Set.eq_univ_of_forall fun q => ?_).symm
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    obtain ⟨k, hk⟩ := hx x
    refine ⟨x - algebraMap K 𝔸[K] k, hk, ?_⟩
    rw [QuotientAddGroup.eq]
    exact ⟨k, by simp⟩

instance t2Space_adeleQuotient : T2Space (AdeleQuotient K) := inferInstance

theorem compactSpace_and_t2Space_adeleQuotient :
    CompactSpace (𝔸[K] ⧸ AdeleRing.principalSubgroup (𝓞 K) K) ∧
      T2Space (𝔸[K] ⧸ AdeleRing.principalSubgroup (𝓞 K) K) :=
  ⟨compactSpace_adeleQuotient K, t2Space_adeleQuotient K⟩

end GroundTheory.Global
