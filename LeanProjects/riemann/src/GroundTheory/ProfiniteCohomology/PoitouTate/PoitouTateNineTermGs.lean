import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.Deduction
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseMain
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {N : ℕ} [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hK : Odd N ∨ IsTotallyComplex K.1)

omit [NeZero N] in

theorem gsBaseCase : ∀ p ∈ N.primeFactors, ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
    CompactDualityHypotheses (gsFinFamily S ιs) (p ^ N.factorization p) (gsRoots S (p ^ N.factorization p))
      (gsCompactInv S ιs (p ^ N.factorization p) (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p))
        (subsingleton_cohomology_three_gsRoots S (mem_of_natCast_dvd_mem S hS (Nat.ordProj_dvd N p))
          (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p)))) U₀ :=
  fun p hp => exists_compactDualityHypotheses_gs S ιs _ p _ (Nat.prime_of_mem_primeFactors hp) rfl
    (mem_of_natCast_dvd_mem S hS (Nat.dvd_of_mem_primeFactors hp)) _ _

variable (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
  (hM : ∀ m : M, N • m = 0)

include hM in

theorem poitouTate_duality_gs {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactDualityMap (gsFinFamily S ιs) (gsRoots S N) h (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) M) :=
  (gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).bijective_compactDualityMap M hM h

include hM in

theorem poitouTate_sha_gs :
    Finite (ptSha (gsFinFamily S ιs) M 1) ∧ Finite (ptSha (gsFinFamily S ιs) (dualRep (gsRoots S N) M) 2) ∧
      Function.Bijective (ptShaPairing (gsFinFamily S ιs) (gsRoots S N) M (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK))) ∧
      Function.Bijective (ptShaPairing (gsFinFamily S ιs) (gsRoots S N) M (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK))).flip :=
  (gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).sha M hM

include hM in

theorem poitouTate_nineTerm_gs :
    Function.Injective (ptGlobalToLocal (gsFinFamily S ιs) M 0).hom ∧
    Function.Exact (ptGlobalToLocal (gsFinFamily S ιs) M 0).hom
      (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 0 + 2 = 2 from rfl)) ∧
    Function.Exact (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 0 + 2 = 2 from rfl))
      (ptDualToGlobal (gsFinFamily S ιs) (gsRoots S N) (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) M (show 1 + 2 = 3 from rfl)
        ((gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).bijective_ptCompactDualMap M hM _)) ∧
    Function.Exact (ptDualToGlobal (gsFinFamily S ιs) (gsRoots S N) (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) M (show 1 + 2 = 3 from rfl)
        ((gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).bijective_ptCompactDualMap M hM _)) (ptGlobalToLocal (gsFinFamily S ιs) M 1).hom ∧
    Function.Exact (ptGlobalToLocal (gsFinFamily S ιs) M 1).hom
      (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 1 + 1 = 2 from rfl)) ∧
    Function.Exact (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 1 + 1 = 2 from rfl))
      (ptDualToGlobal (gsFinFamily S ιs) (gsRoots S N) (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) M (show 2 + 1 = 3 from rfl)
        ((gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).bijective_ptCompactDualMap M hM _)) ∧
    Function.Exact (ptDualToGlobal (gsFinFamily S ιs) (gsRoots S N) (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) M (show 2 + 1 = 3 from rfl)
        ((gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).bijective_ptCompactDualMap M hM _)) (ptGlobalToLocal (gsFinFamily S ιs) M 2).hom ∧
    Function.Exact (ptGlobalToLocal (gsFinFamily S ιs) M 2).hom
      (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 2 + 0 = 2 from rfl)) ∧
    Function.Surjective (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 2 + 0 = 2 from rfl)) :=
  (gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).nineTerm M hM

end GroundTheory.ProfCoh
