import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.RealEvenHyp
import GroundTheory.ProfiniteCohomology.PoitouTate.RealOddMain
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

section Nonempty

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) {N : ℕ}

theorem nonempty_of_natCast_mem_of_ne_one (hN : N ≠ 1)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) : Nonempty S := by
  obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd hN
  obtain ⟨k, rfl⟩ := hpN
  refine nonempty_of_natCast_mem S p hp fun v hv => hS v ?_
  rw [Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ hv

end Nonempty

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S] [Nonempty S]
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {N : ℕ} [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

section Hypotheses

set_option maxHeartbeats 1000000 in
include hS in

theorem gsTrace_eq_gsOddTrace (hodd : Odd N) : gsTrace S ιr ιs N = gsOddTrace S ιr ιs hS hodd := by
  have : Finite (gsRoots S N) :=
    (nonempty_addEquiv_gsRoots_of_mem S hS).elim fun e => Finite.of_equiv _ e.toEquiv.symm
  refine AddMonoidHom.ext fun z => ?_
  obtain ⟨ξ, hξ⟩ := (gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).surjective_ptTLocalToCompact_two
    (gsRoots S N) (nsmul_gsRoots S N) z
  calc gsTrace S ιr ιs N z
      = gsTrace S ιr ιs N ((ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom ξ) :=
        congrArg _ hξ.symm
    _ = gsOddTrace S ιr ιs hS hodd
          ((ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom ξ) :=
        zmodToQZ_injective ((gsTrace_localToCompact S ιr ιs N ξ).trans
          (gsOddTrace_localToCompact S ιr ιs hS hodd ξ).symm)
    _ = gsOddTrace S ιr ιs hS hodd z := congrArg _ hξ

include hS in

theorem gsTatePoitouTateHypotheses :
    TatePoitouTateHypotheses (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
      (gsTrace S ιr ιs N) (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) := by
  rcases Nat.even_or_odd N with hev | hodd
  · exact gsEvenTatePoitouTateHypotheses S ιr ιs hS hev
  · exact (gsTrace_eq_gsOddTrace S ιr ιs hS hodd).symm ▸ gsOddTatePoitouTateHypotheses S ιr ιs hS hodd

end Hypotheses

variable (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
  (hM : ∀ m : M, N • m = 0)

include hS hM in

theorem poitouTateReal_duality {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    Function.Bijective (tateCompactDualityMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) h
      (gsTrace S ιr ιs N) M) :=
  (gsTatePoitouTateHypotheses S ιr ιs hS).duality M hM h hs

include hS hM in

theorem poitouTateReal_compactDual {r s : ℕ} (h : r + s = 3) (hr : 1 ≤ r) :
    Function.Bijective (ptTCompactDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
      (gsTrace S ιr ιs N) h) :=
  (gsTatePoitouTateHypotheses S ιr ιs hS).bijective_ptTCompactDualMap M hM h hr

include hS hM in

theorem poitouTateReal_nineTerm :
    Function.Injective (ptTGlobalToLocalHat (gsFinFamily S ιs) (gsRealFamily S ιr) M) ∧
    Function.Exact (ptTGlobalToLocalHat (gsFinFamily S ιs) (gsRealFamily S ιr) M)
      (ptTLocalHatDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N)) ∧
    Function.Exact (ptTLocalHatDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N))
      (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) (gsTrace S ιr ιs N) M
        (show 1 + 2 = 3 from rfl)
        ((gsTatePoitouTateHypotheses S ιr ιs hS).bijective_ptTCompactDualMap M hM _ le_rfl)) ∧
    Function.Exact (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
        (gsTrace S ιr ιs N) M (show 1 + 2 = 3 from rfl)
        ((gsTatePoitouTateHypotheses S ιr ιs hS).bijective_ptTCompactDualMap M hM _ le_rfl))
      (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 1).hom ∧
    Function.Exact (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 1).hom
      (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 1 + 1 = 2 from rfl)) ∧
    Function.Exact (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 1 + 1 = 2 from rfl))
      (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) (gsTrace S ιr ιs N) M
        (show 2 + 1 = 3 from rfl)
        ((gsTatePoitouTateHypotheses S ιr ιs hS).bijective_ptTCompactDualMap M hM _ (by norm_num))) ∧
    Function.Exact (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
        (gsTrace S ιr ιs N) M (show 2 + 1 = 3 from rfl)
        ((gsTatePoitouTateHypotheses S ιr ιs hS).bijective_ptTCompactDualMap M hM _ (by norm_num)))
      (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 2).hom ∧
    Function.Exact (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 2).hom
      (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 2 + 0 = 2 from rfl)) ∧
    Function.Surjective (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
      (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 2 + 0 = 2 from rfl)) :=
  (gsTatePoitouTateHypotheses S ιr ιs hS).nineTerm M hM

include hS hM in

theorem poitouTateReal_sha :
    Finite (ptTSha (gsFinFamily S ιs) (gsRealFamily S ιr) M 1) ∧
      Finite (ptTSha (gsFinFamily S ιs) (gsRealFamily S ιr) (dualRep (gsRoots S N) M) 2) ∧
      Function.Bijective (ptTShaPairing (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsTrace S ιr ιs N)) ∧
      Function.Bijective (ptTShaPairing (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsTrace S ιr ιs N)).flip :=
  (gsTatePoitouTateHypotheses S ιr ιs hS).sha M hM

include ιs hS hM in

theorem injective_gsRealRes_three : Function.Injective (gsRealRes S ιr M 3).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have h0 : (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 3).hom x = 0 := by
    refine (ptTGlobalToLocal_apply _ _ M 3 x).trans (Prod.ext (funext fun v => ?_) (funext fun w => ?_))
    · exact (subsingleton_cohomology_gsFinFamily_of_three_le S ιs (NeZero.ne N) M hM v le_rfl).elim _ _
    · exact congrFun hx w
  exact (gsTatePoitouTateHypotheses S ιr ιs hS).injective_ptTGlobalToLocal_three M hM
    (h0.trans (map_zero _).symm)

include ιs hS hM in

theorem bijective_gsRealRes {r : ℕ} (hr : 3 ≤ r) : Function.Bijective (gsRealRes S ιr M r).hom := by
  refine ⟨?_, surjective_gsRealRes_of_three_le S ιr (NeZero.ne N) hS M hM hr⟩
  rcases r with _ | _ | _ | _ | r
  · exact absurd hr (by norm_num)
  · exact absurd hr (by norm_num)
  · exact absurd hr (by norm_num)
  · exact injective_gsRealRes_three S ιr ιs hS M hM
  · exact injective_gsRealRes_of_four_le S ιr (NeZero.ne N) hS M hM (by omega)

end GroundTheory.ProfCoh
