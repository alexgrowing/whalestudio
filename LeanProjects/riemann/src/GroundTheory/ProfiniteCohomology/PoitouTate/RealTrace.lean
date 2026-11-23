import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.RealOdd
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingUnitsDiv
import GroundTheory.ProfiniteCohomology.CupProducts.Projection
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.RealPlaces
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (N : ℕ) [NeZero N]

theorem gsRealInvRootsQZ_ptRes (w : {v : InfinitePlace K.1 // v.IsReal}) (x : cohomology (gsRoots S N) 2) :
    gsRealInvRootsQZ S ιr N w (ptRes (gsRealFamily S ιr) (gsRoots S N) w 2 x) =
      placeInv (.inl w.1) (realLocalEquiv w 2 ((realUnitsRes S ιr 2 w).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) N) 2).hom x))) := by
  have hmor : 𝟙 _ ≫ gsRealRootsToUnits S ιr N w =
      (Rep.resFunctor (gsRealFamily S ιr w).toMonoidHom).map
        (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) N) ≫ realUnitsMor S ιr w :=
    Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  have key : (cohomologyMap (gsRealRootsToUnits S ιr N w) 2).hom
      (ptRes (gsRealFamily S ιr) (gsRoots S N) w 2 x) =
      (realUnitsRes S ιr 2 w).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) N) 2).hom x) :=
    (cohomologyMap_cohomologyMapAlong _ _ _ _ x).trans
      ((congrArg (fun f => (cohomologyMapAlong (gsRealFamily S ιr w).toMonoidHom
        (continuous_toMonoidHom _) f 2).hom x) hmor).trans
        (cohomologyMapAlong_cohomologyMap _ _ _ _ x).symm)
  exact (gsRealInvRootsQZ_apply S ιr N w _).trans
    ((realInv_eq_placeInv w.1 _).trans (congrArg _ (congrArg _ key)))

theorem gsLocalInvRootsQZ_ptRes_eq (v : S) (x : cohomology (gsRoots S N) 2) :
    gsLocalInvRootsQZ S ιs N v (ptRes (gsFinFamily S ιs) (gsRoots S N) v 2 x) =
      placeInv (.inr (v : HeightOneSpectrum (𝓞 K.1))) (brauerLocal (gsLocalEmbeddings S ιs)
        (sUnitsBrauer K S ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) N) 2).hom x))
        (.inr (v : HeightOneSpectrum (𝓞 K.1)))) := by
  refine (gsLocalInvRootsQZ_cohomologyMapAlong S ιs N v x).trans (Eq.symm ?_)
  refine (congrArg (fun z => placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
    (brauerLocal (gsLocalEmbeddings S ιs) z (.inr (v : HeightOneSpectrum (𝓞 K.1)))))
    (sUnitsBrauer_apply K S _)).trans ?_
  refine (congrArg (placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1))))
    (brauerLocal_gsBrauerInfl_inr K S _ _ _)).trans ?_
  refine (placeInv_inr_apply _ _).trans ?_
  simp only [gsLocalEmbeddings_fin]

theorem gsRealInvRootsQZ_ptRes_eq (w : {v : InfinitePlace K.1 // v.IsReal}) (x : cohomology (gsRoots S N) 2) :
    gsRealInvRootsQZ S ιr N w (ptRes (gsRealFamily S ιr) (gsRoots S N) w 2 x) =
      placeInv (.inl w.1) (brauerLocal (gsLocalEmbeddings S ιs)
        (sUnitsBrauer K S ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) N) 2).hom x))
        (.inl w.1)) :=
  (gsRealInvRootsQZ_ptRes S ιr N w x).trans (congrArg (placeInv (K := K) (.inl w.1))
    (realLocalEquiv_realUnitsRes S ιr (gsLocalEmbeddings S ιs) (by norm_num) w _).symm)

omit [NeZero N] in

theorem sum_placeInv_inr_add_sum_placeInv_inl [Fintype S] (ι : LocalEmbeddings K) (z : cohomology (unitsLimitRep K) 2)
    (hz : ∀ v : HeightOneSpectrum (𝓞 K.1), v ∉ S → brauerLocal ι z (.inr v) = 0) :
    ∑ v : S, placeInv (.inr (v : HeightOneSpectrum (𝓞 K.1))) (brauerLocal ι z (.inr (v : HeightOneSpectrum (𝓞 K.1)))) +
      ∑ w : {v : InfinitePlace K.1 // v.IsReal}, placeInv (.inl w.1) (brauerLocal ι z (.inl w.1)) = 0 := by
  classical
  let A : Finset (Place K.1) := Finset.univ.image fun v : S => (Sum.inr (v : HeightOneSpectrum (𝓞 K.1)) : Place K.1)
  let B : Finset (Place K.1) := Finset.univ.image fun w : {v : InfinitePlace K.1 // v.IsReal} =>
    (Sum.inl w.1 : Place K.1)
  have hzT : ∀ p ∉ A ∪ B, placeInv p (brauerLocal ι z p) = 0 := by
    intro p hp
    rcases p with w | v
    · have hw : ¬ w.IsReal := fun h => hp (Finset.mem_union_right _
        (Finset.mem_image.2 ⟨⟨w, h⟩, Finset.mem_univ _, rfl⟩))
      have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hw
      have : Subsingleton (localGaloisCohomology K 2 (.inl w)) :=
        subsingleton_cohomology_two_of_isComplex w hc
      exact (congrArg (placeInv (.inl w)) (Subsingleton.elim _ 0)).trans (map_zero _)
    · have hv : v ∉ S := fun h => hp (Finset.mem_union_left _
        (Finset.mem_image.2 ⟨⟨v, h⟩, Finset.mem_univ _, rfl⟩))
      rw [hz v hv, map_zero]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hpA
    obtain ⟨w, -, hw⟩ := Finset.mem_image.1 hpB
    exact Sum.inl_ne_inr hw
  have hsum : brauerSumInv ι z = ∑ v : S, placeInv (.inr (v : HeightOneSpectrum (𝓞 K.1)))
      (brauerLocal ι z (.inr (v : HeightOneSpectrum (𝓞 K.1)))) +
      ∑ w : {v : InfinitePlace K.1 // v.IsReal}, placeInv (.inl w.1) (brauerLocal ι z (.inl w.1)) := by
    refine (AddMonoidHom.comp_apply _ _ _).trans ?_
    rw [sumPlaceInv_eq_sum_of_placeInv (A ∪ B) _ hzT, Finset.sum_union hdisj,
      Finset.sum_image (fun v _ w _ h => Subtype.ext (Sum.inr_injective h)),
      Finset.sum_image (fun v _ w _ h => Subtype.ext (Sum.inl_injective h))]
  exact hsum.symm.trans (brauerSumInv_eq_zero ι z)

theorem gsReciprocityReal [Fintype S] (x : cohomology (gsRoots S N) 2) :
    ∑ v, gsLocalInvRootsQZ S ιs N v (ptRes (gsFinFamily S ιs) (gsRoots S N) v 2 x) +
      ∑ w, gsRealInvRootsQZ S ιr N w (ptRes (gsRealFamily S ιr) (gsRoots S N) w 2 x) = 0 :=
  (congrArg₂ (· + ·) (Finset.sum_congr rfl fun v _ => gsLocalInvRootsQZ_ptRes_eq S ιs N v x)
    (Finset.sum_congr rfl fun w _ => gsRealInvRootsQZ_ptRes_eq S ιr ιs N w x)).trans
    (sum_placeInv_inr_add_sum_placeInv_inl S (gsLocalEmbeddings S ιs) _
      (fun v hv => brauerLocal_sUnitsBrauer_inr K S _ _ v hv))

def gsSumInvReal [Fintype S] : ptTLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2 →+ QZ where
  toFun ξ := ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) + ∑ w, gsRealInvRootsQZ S ιr N w (ξ.2 w)
  map_zero' := by
    refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun v _ => map_zero _)
      (Finset.sum_eq_zero fun w _ => map_zero _)).trans (add_zero 0)
  map_add' ξ η := by
    change ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v + η.1 v) + ∑ w, gsRealInvRootsQZ S ιr N w (ξ.2 w + η.2 w) = _
    simp only [map_add, Finset.sum_add_distrib]
    abel

omit [NeZero N] in
theorem gsSumInvReal_apply [Fintype S] (ξ : ptTLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2) :
    gsSumInvReal S ιr ιs N ξ =
      ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) + ∑ w, gsRealInvRootsQZ S ιr N w (ξ.2 w) :=
  rfl

theorem gsSumInvReal_eq_zero_of [Fintype S] (ξ : ptTLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2)
    (hξ : (ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom ξ = 0) :
    gsSumInvReal S ιr ιs N ξ = 0 := by
  have e := ptTExact_local (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 1
  have e2 := (e ξ).1 hξ
  obtain ⟨x, hx⟩ := e2
  exact (congrArg (gsSumInvReal S ιr ιs N) hx.symm).trans
    ((congrArg (gsSumInvReal S ιr ιs N) (ptTGlobalToLocal_apply _ _ (gsRoots S N) 2 x)).trans
      (gsReciprocityReal S ιr ιs N x))

end GroundTheory.ProfCoh
