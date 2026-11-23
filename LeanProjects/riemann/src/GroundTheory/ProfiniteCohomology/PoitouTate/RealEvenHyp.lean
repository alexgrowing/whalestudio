import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.RealEvenTau
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

section Hypotheses

variable [Fintype S] {N : ℕ} [NeZero N]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (hev : Even N)

include hS hev in

theorem gsTauBijective_of_le (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ (2 * N) = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hU : U ≤ W₀) : GsTauBijective S ιs (N := N) U := by
  obtain ⟨L, _, hL, rfl⟩ := exists_gsOpenSubgroup_eq K S U
  exact gsTauBijective_gsOpenSubgroup S ιs hS hev hL W₀ hW₀ hU

set_option maxHeartbeats 1000000 in
include hS hev in

theorem bijective_tateCompactDualityMap_coind_gs_of_even
    (t : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N)
    (ht : Function.Surjective t) (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ (2 * N) = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hU : U ≤ W₀) {r s : ℕ} (h : r + (s + 1) = 3)
    [IsDiscreteRep (dualRep (gsRoots S N) (Rep.coind (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
      (zmodRep.{0} (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) N)))] :
    Function.Bijective (tateCompactDualityMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) h t
      (Rep.coind (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (zmodRep.{0} (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) N))) := by
  have hfree := freeOnCosets_gsRealFamily_of_le S ιr hS hev W₀ hW₀ U hU
  refine bijective_tateCompactDualityMap_coind (gsFinFamily S ιs) (gsRealFamily S ιr) U hfree
    (nsmul_gsRoots S N) t h ?_
  have : Finite (gsRoots S N) :=
    (nonempty_addEquiv_gsRoots_of_mem S hS).elim fun e => Finite.of_equiv _ e.toEquiv.symm
  have hτ : Function.Surjective (tateCoresTrace (gsFinFamily S ιs) (gsRealFamily S ιr) U hfree t) :=
    ht.comp (surjective_tateCompactCores_three (gsFinFamily S ιs) (gsRealFamily S ιr) U hfree (gsRoots S N)
      (nsmul_gsRoots S N) fun M _ _ hM => subsingleton_gsTateCompactCohomology S ιr ιs (NeZero.ne N) hS M hM
        le_rfl)
  have hb := gsTauBijective_of_le S ιs hS hev W₀ hW₀ U hU
    (tateCoresTrace (gsFinFamily S ιs) (gsRealFamily S ιr) U hfree t) hτ h
  convert hb using 1

include hS hev in

theorem exists_tateCompactDualityHypotheses_gs_of_even
    (t : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N)
    (ht : Function.Surjective t) :
    ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      TateCompactDualityHypotheses (gsFinFamily S ιs) (gsRealFamily S ιr) N (gsRoots S N) t U₀ := by
  have hn0 : 2 * N ≠ 0 := by have := NeZero.ne N; omega
  obtain ⟨W₀, hW₀⟩ := exists_openSubgroup_fixing_rootsOfUnity K S (2 * N) hn0
  refine ⟨W₀, ⟨nonempty_addEquiv_gsRoots_of_mem S hS, fun M _ _ hM =>
    subsingleton_gsTateCompactCohomology S ιr ιs (NeZero.ne N) hS M hM le_rfl, fun U hU {r s} h hs => ?_⟩⟩
  cases s with
  | zero => exact absurd hs (by norm_num)
  | succ s =>
    have : Finite (Rep.coind (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (zmodRep.{0} (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) N)) := finite_coind U _
    have : IsDiscreteRep (dualRep (gsRoots S N) (Rep.coind (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (zmodRep.{0} (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) N))) := isDiscreteRep_dualRep _ _
    convert bijective_tateCompactDualityMap_coind_gs_of_even S ιr ιs hS hev t ht W₀ hW₀ U hU h using 1

include hS hev in

theorem bijective_tateCompactDualityMap_gs_of_even
    (t : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N)
    (ht : Function.Surjective t) (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))
    [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, N • m = 0) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    Function.Bijective (tateCompactDualityMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) h t M) :=
  (exists_tateCompactDualityHypotheses_gs_of_even S ιr ιs hS hev t ht).elim fun _ H =>
    H.bijective_tateCompactDualityMap M hM h hs

include hS hev in

theorem gsEvenTatePoitouTateHypotheses :
    TatePoitouTateHypotheses (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
      (gsTrace S ιr ιs N) (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) := by
  have : Nonempty S := nonempty_of_natCast_mem S 2 Nat.prime_two (mem_of_natCast_two_mem_of_even S hS hev)
  have hD := nonempty_addEquiv_gsRoots_of_mem S hS
  have ht := surjective_of_localToCompact_two S ιr ιs hS (gsTrace S ιr ιs N) (gsTrace_localToCompact S ιr ιs N)
  exact
    { nonempty_addEquiv := hD
      duality := @fun M _ _ hM r s h hs =>
        bijective_tateCompactDualityMap_gs_of_even S ιr ιs hS hev (gsTrace S ιr ιs N) ht M hM h hs
      finite_cohomology := fun M _ _ hM r hr =>
        finite_cohomology_gs K S M (fun v hv => hS v (natCast_mem_of_natCard_mem v.isPrime hM hv)) r hr
      localToCompact_two := gsTrace_localToCompact S ιr ιs N
      injective_res_zero := fun M _ => injective_ptRes_zero_gs S ιs M
      surjective_localPairing_zero := fun M _ _ hM v => (bijective_gsLocalPairing S ιs N hD M hM v _).2
      surjective_localPairing_two := fun M _ _ hM v => (bijective_gsLocalPairing S ιs N hD M hM v _).2
      surjective_realPairing_zero := fun M _ _ hM w => surjective_gsRealPairing_zero S ιr N M hD hM w
      surjective_realPairing_two := fun M _ _ hM w χ hχ => exists_gsRealPairing_two S ιr N M hD hM w χ hχ }

end Hypotheses

end GroundTheory.ProfCoh
