import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SurjectiveOfInjectiveOfInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.LocalField
  GroundTheory.LocalField.Abstract

open scoped GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Degree

variable {K : FiniteSubfield} (w : HeightOneSpectrum (𝓞 K.1))

set_option maxHeartbeats 2000000 in

theorem eq_univ_of_unramifiedDegree
    (σ : Gal(AlgebraicClosure (w.adicCompletion K.1)/w.adicCompletion K.1))
    (hσ : unramifiedDegree (w.adicCompletion K.1) (AlgebraicClosure (w.adicCompletion K.1)) σ =
      Multiplicative.ofAdd 1)
    (E : Set Gal(AlgebraicClosure (w.adicCompletion K.1)/w.adicCompletion K.1)) (hE : IsClosed E)
    (hpow : ∀ k : ℤ, σ ^ k ∈ E)
    (hmul : ∀ g ∈ E, ∀ h, unramifiedDegree (w.adicCompletion K.1)
      (AlgebraicClosure (w.adicCompletion K.1)) h = 1 → g * h ∈ E) :
    E = Set.univ := by
  set deg := unramifiedDegree (w.adicCompletion K.1) (AlgebraicClosure (w.adicCompletion K.1))
  have hT : IsClosed (deg '' E) := (hE.isCompact.image continuous_unramifiedDegree).isClosed
  have hsub : (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) ⊆ deg '' E := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨σ ^ k, hpow k, by rw [map_zpow, hσ]⟩
  have huniv : deg '' E = Set.univ := by
    have hd := dense_zpowers_ofAdd_one.mono hsub
    rw [← hT.closure_eq, hd.closure_eq]
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨e, he, hde⟩ : deg x ∈ deg '' E := by
    rw [huniv]
    exact Set.mem_univ _
  have hx : x = e * (e⁻¹ * x) := by group
  rw [hx]
  refine hmul e he _ ?_
  rw [map_mul, map_inv, hde, inv_mul_cancel]

end Degree

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ιs : LocalEmbeddings K)
  (v : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S})

theorem gsDecomp_eq_one_of_unramifiedDegree_eq_one
    (g : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1))
    (hg : unramifiedDegree (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) g = 1) :
    gsDecomp K S ιs v g = 1 :=
  decompHomS_eq_one_of_unramifiedDegree_eq_one S (ιs.fin v.1) v.2 g hg

theorem continuous_rangeRestrict_gsDecomp : Continuous (gsDecomp K S ιs v).rangeRestrict :=
  (continuous_gsDecomp K S ιs v).subtype_mk _

instance t2Space_galUnramifiedOutside : T2Space (galUnramifiedOutside K.1 ℚ̄ S) :=
  galois_t2Space K.1 (maxUnramifiedOutside K.1 ℚ̄ S)

instance compactSpace_range_gsDecomp : CompactSpace (gsDecomp K S ιs v).range := by
  refine isCompact_iff_compactSpace.mp ?_
  rw [MonoidHom.coe_range]
  exact isCompact_range (continuous_gsDecomp K S ιs v)

theorem isClosed_range_gsDecomp : IsClosed ((gsDecomp K S ιs v).range : Set (galUnramifiedOutside K.1 ℚ̄ S)) := by
  rw [MonoidHom.coe_range]
  exact (isCompact_range (continuous_gsDecomp K S ιs v)).isClosed

theorem isQuotientMap_rangeRestrict_gsDecomp : Topology.IsQuotientMap (gsDecomp K S ιs v).rangeRestrict :=
  ((continuous_rangeRestrict_gsDecomp K S ιs v).isClosedMap).isQuotientMap
    (continuous_rangeRestrict_gsDecomp K S ιs v) (MonoidHom.rangeRestrict_surjective _)

set_option maxHeartbeats 2000000 in

theorem isTopologicalGenerator_rangeRestrict_gsDecomp
    (σ : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1))
    (hσ : unramifiedDegree (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) σ =
      Multiplicative.ofAdd 1) :
    IsTopologicalGenerator ((gsDecomp K S ιs v).rangeRestrict σ) := by
  set f := (gsDecomp K S ιs v).rangeRestrict
  set C := closure (Subgroup.zpowers (f σ) : Set (gsDecomp K S ιs v).range)
  have hE := eq_univ_of_unramifiedDegree v.1 σ hσ (f ⁻¹' C)
    (isClosed_closure.preimage (continuous_rangeRestrict_gsDecomp K S ιs v))
    (fun k => subset_closure (by rw [map_zpow]; exact Subgroup.zpow_mem_zpowers _ k))
    (fun g hg h hh => by
      have h1 : f h = 1 := Subtype.ext (gsDecomp_eq_one_of_unramifiedDegree_eq_one K S ιs v h hh)
      rw [Set.mem_preimage, map_mul, h1, mul_one]
      exact hg)
  rw [IsTopologicalGenerator, dense_iff_closure_eq]
  refine Set.eq_univ_of_forall fun z => ?_
  obtain ⟨g, rfl⟩ := MonoidHom.rangeRestrict_surjective _ z
  have : g ∈ f ⁻¹' C := by rw [hE]; exact Set.mem_univ _
  exact this

end

end GroundTheory.ProfCoh
