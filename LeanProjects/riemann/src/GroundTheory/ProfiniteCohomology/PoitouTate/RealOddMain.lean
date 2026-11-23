import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.RealOdd
import GroundTheory.ProfiniteCohomology.RealPlaces.Vanishing
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S] [Nonempty S]
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {N : ℕ} [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hodd : Odd N)
  (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
  (hM : ∀ m : M, N • m = 0)

include hM in

theorem poitouTateReal_nineTerm_of_odd :
    Function.Injective (ptTGlobalToLocalHat (gsFinFamily S ιs) (gsRealFamily S ιr) M) ∧
    Function.Exact (ptTGlobalToLocalHat (gsFinFamily S ιs) (gsRealFamily S ιr) M)
      (ptTLocalHatDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N)) ∧
    Function.Exact (ptTLocalHatDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N))
      (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) (gsOddTrace S ιr ιs hS hodd) M
        (show 1 + 2 = 3 from rfl)
        ((gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).bijective_ptTCompactDualMap M hM _ le_rfl)) ∧
    Function.Exact (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
        (gsOddTrace S ιr ιs hS hodd) M (show 1 + 2 = 3 from rfl)
        ((gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).bijective_ptTCompactDualMap M hM _ le_rfl))
      (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 1).hom ∧
    Function.Exact (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 1).hom
      (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 1 + 1 = 2 from rfl)) ∧
    Function.Exact (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 1 + 1 = 2 from rfl))
      (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) (gsOddTrace S ιr ιs hS hodd) M
        (show 2 + 1 = 3 from rfl)
        ((gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).bijective_ptTCompactDualMap M hM _ (by norm_num))) ∧
    Function.Exact (ptTDualToGlobal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N)
        (gsOddTrace S ιr ιs hS hodd) M (show 2 + 1 = 3 from rfl)
        ((gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).bijective_ptTCompactDualMap M hM _ (by norm_num)))
      (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 2).hom ∧
    Function.Exact (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 2).hom
      (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 2 + 0 = 2 from rfl)) ∧
    Function.Surjective (ptTLocalDualMap (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
      (gsLocalInvRootsQZ S ιs N) (gsRealInvRootsQZ S ιr N) (show 2 + 0 = 2 from rfl)) :=
  (gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).nineTerm M hM

include hM in

theorem poitouTateReal_sha_of_odd :
    Finite (ptTSha (gsFinFamily S ιs) (gsRealFamily S ιr) M 1) ∧
      Finite (ptTSha (gsFinFamily S ιs) (gsRealFamily S ιr) (dualRep (gsRoots S N) M) 2) ∧
      Function.Bijective (ptTShaPairing (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsOddTrace S ιr ιs hS hodd)) ∧
      Function.Bijective (ptTShaPairing (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) M
        (gsOddTrace S ιr ιs hS hodd)).flip :=
  (gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).sha M hM

include ιs hS hodd hM in

theorem injective_gsRealRes_three_of_odd : Function.Injective (gsRealRes S ιr M 3).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have h0 : (ptTGlobalToLocal (gsFinFamily S ιs) (gsRealFamily S ιr) M 3).hom x = 0 := by
    refine (ptTGlobalToLocal_apply _ _ M 3 x).trans (Prod.ext (funext fun v => ?_) (funext fun w => ?_))
    · exact (subsingleton_cohomology_gsFinFamily_of_three_le S ιs (NeZero.ne N) M hM v le_rfl).elim _ _
    · exact congrFun hx w
  exact (gsOddTatePoitouTateHypotheses S ιr ιs hS hodd).injective_ptTGlobalToLocal_three M hM
    (h0.trans (map_zero _).symm)

include ιs hS hodd hM in

theorem bijective_gsRealRes_of_odd {r : ℕ} (hr : 3 ≤ r) : Function.Bijective (gsRealRes S ιr M r).hom := by
  refine ⟨?_, surjective_gsRealRes_of_three_le S ιr (NeZero.ne N) hS M hM hr⟩
  rcases r with _ | _ | _ | _ | r
  · exact absurd hr (by norm_num)
  · exact absurd hr (by norm_num)
  · exact absurd hr (by norm_num)
  · exact injective_gsRealRes_three_of_odd S ιr ιs hS hodd M hM
  · exact injective_gsRealRes_of_four_le S ιr (NeZero.ne N) hS M hM (by omega)

end GroundTheory.ProfCoh
