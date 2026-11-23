import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormationAlt
import GroundTheory.ProfiniteCohomology.ClassFormations.Corestriction
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.QuotientToInvariantsFunctorPreservesZeroMorphism
import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section CoresNaturality

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

theorem coindMap_res_comp_coindTrace (U : OpenSubgroup G) {A B : Rep.{u} k G} (φ : A ⟶ B) :
    Rep.coindMap (U : Subgroup G).subtype ((Rep.resFunctor (U : Subgroup G).subtype).map φ) ≫
        coindTrace (U : Subgroup G) B =
      coindTrace (U : Subgroup G) A ≫ φ := by
  ext f
  change (coindTrace (U : Subgroup G) B).hom
      ((Rep.coindMap (U : Subgroup G).subtype ((Rep.resFunctor (U : Subgroup G).subtype).map φ)).hom f) =
    φ.hom ((coindTrace (U : Subgroup G) A).hom f)
  rw [coindTrace_hom_apply, coindTrace_hom_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  induction c using QuotientGroup.induction_on with
  | H x =>
    rw [coindTraceTerm_apply, coindTraceTerm_apply]
    change B.ρ x (φ.hom (f.1 x⁻¹)) = φ.hom (A.ρ x (f.1 x⁻¹))
    rw [Rep.hom_comm_apply]

theorem cohomologyCores_naturality (U : OpenSubgroup G) {A B : Rep.{u} k G} [IsDiscreteRep A]
    [IsDiscreteRep B] (φ : A ⟶ B) (n : ℕ) :
    cohomologyCores U A n ≫ cohomologyMap φ n =
      cohomologyMap ((Rep.resFunctor (U : Subgroup G).subtype).map φ) n ≫ cohomologyCores U B n := by
  rw [cohomologyCores, cohomologyCores, Category.assoc, ← cohomologyMap_comp,
    ← coindMap_res_comp_coindTrace, cohomologyMap_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, shapiroMap_naturality]

theorem cohomologyCoresLE_naturality {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    (φ : A ⟶ B) {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ) :
    cohomologyCoresLE A h n ≫ cohomologyMap ((Rep.resFunctor (U : Subgroup G).subtype).map φ) n =
      cohomologyMap ((Rep.resFunctor (V : Subgroup G).subtype).map φ) n ≫
        cohomologyCoresLE B h n := by
  have h1 := cohomologyCores_naturality (openSubgroupOf U V)
    ((Rep.resFunctor (U : Subgroup G).subtype).map φ) n
  have h2 : cohomologyMap ((Rep.resFunctor (V : Subgroup G).subtype).map φ) n ≫
      cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from h)).toMonoidHom
        (continuous_subgroupOfEquivOfLe _) (resSubgroupOfInvHom _ B) n =
      cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from h)).toMonoidHom
        (continuous_subgroupOfEquivOfLe _) (resSubgroupOfInvHom _ A) n ≫
      cohomologyMap ((Rep.resFunctor ((V : Subgroup G).subgroupOf U).subtype).map
        ((Rep.resFunctor (U : Subgroup G).subtype).map φ)) n := by
    rw [← cohomologyMapAlong_id_eq_cohomologyMap, ← cohomologyMapAlong_id_eq_cohomologyMap,
      ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_congr _ _ _ _ (MonoidHom.ext fun _ => rfl) (fun _ => rfl) n
  rw [cohomologyCoresLE_eq, cohomologyCoresLE_eq, Category.assoc, h1, ← Category.assoc,
    ← Category.assoc, ← h2]

theorem cohomologyCoresLE_cohomologyMap {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    (φ : A ⟶ B) {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ)
    (x : cohomology (Rep.res (V : Subgroup G).subtype A) n) :
    (cohomologyCoresLE B h n).hom
        ((cohomologyMap ((Rep.resFunctor (V : Subgroup G).subtype).map φ) n).hom x) =
      (cohomologyMap ((Rep.resFunctor (U : Subgroup G).subtype).map φ) n).hom
        ((cohomologyCoresLE A h n).hom x) :=
  (congrArg (fun ψ => ψ.hom x) (cohomologyCoresLE_naturality φ h n)).symm

end CoresNaturality

section Kummer

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

theorem nonempty_addEquiv_galRootsOfUnity {n : ℕ} (hn : (n : K) ≠ 0) :
    Nonempty (galRootsOfUnity.{0} K Ksep n ≃+ ZMod n) := by
  have : IsSepClosed Ksep := IsSepClosure.sep_closed K
  have hn' : (n : Ksep) ≠ 0 := by
    rw [← map_natCast (algebraMap K Ksep)]
    exact (map_ne_zero _).2 hn
  have : NeZero (n : Ksep) := ⟨hn'⟩
  have : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  have hcard : Nat.card (rootsOfUnity n Ksep) = Nat.card (Multiplicative (ZMod n)) := by
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  exact ⟨MulEquiv.toAdditive (mulEquivOfCyclicCardEq hcard)⟩

abbrev kummerSeqOpen (n : ℕ) (W : Subgroup Gal(Ksep/K)) : ShortComplex (Rep (ULift.{0} ℤ) W) where
  X₁ := Rep.res W.subtype (galRootsOfUnity.{0} K Ksep n)
  X₂ := Rep.res W.subtype (galUnits.{0} K Ksep)
  X₃ := Rep.res W.subtype (galUnits.{0} K Ksep)
  f := (Rep.resFunctor W.subtype).map (kummerSequence K Ksep n).f
  g := (Rep.resFunctor W.subtype).map (kummerSequence K Ksep n).g
  zero := ((kummerSequence K Ksep n).map (Rep.resFunctor W.subtype)).zero

instance isDiscreteRep_res_galRootsOfUnity_subgroup (n : ℕ) (W : Subgroup Gal(Ksep/K)) :
    IsDiscreteRep (Rep.res W.subtype (galRootsOfUnity.{0} K Ksep n)) :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_res_galUnits_subgroup (W : Subgroup Gal(Ksep/K)) :
    IsDiscreteRep (Rep.res W.subtype (galUnits.{0} K Ksep)) :=
  isDiscreteRep_res_subtype _ _

theorem kummerSeqOpen_shortExact {n : ℕ} (hn : (n : K) ≠ 0) (W : Subgroup Gal(Ksep/K)) :
    (kummerSeqOpen (K := K) (Ksep := Ksep) n W).ShortExact :=
  shortExact_map_res W (kummerSequence_shortExact n hn)

omit [IsSepClosure K Ksep] in

theorem kummerSeqOpen_g_hom_apply (n : ℕ) (W : Subgroup Gal(Ksep/K))
    (x : Rep.res W.subtype (galUnits.{0} K Ksep)) :
    (kummerSeqOpen (K := K) (Ksep := Ksep) n W).g.hom x = n • x :=
  nsmul_id_hom_apply (galUnits.{0} K Ksep) n x

omit [IsSepClosure K Ksep] in
theorem kummerSeqOpen_g (n : ℕ) (W : Subgroup Gal(Ksep/K)) :
    (kummerSeqOpen (K := K) (Ksep := Ksep) n W).g = n • 𝟙 (Rep.res W.subtype (galUnits.{0} K Ksep)) :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x =>
    (kummerSeqOpen_g_hom_apply n W x).trans
      (nsmul_id_hom_apply (Rep.res W.subtype (galUnits.{0} K Ksep)) n x).symm))

theorem cohomologyMap_kummerSeqOpen_g_apply (n : ℕ) (W : Subgroup Gal(Ksep/K)) (i : ℕ)
    (y : cohomology (Rep.res W.subtype (galUnits.{0} K Ksep)) i) :
    (cohomologyMap (kummerSeqOpen (K := K) (Ksep := Ksep) n W).g i).hom y = n • y := by
  rw [kummerSeqOpen_g]
  exact cohomologyMap_nsmul_id_apply _ n i y

end Kummer

section Local

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ}

attribute [local irreducible] localClassFormationOfIsSepClosure

theorem subsingleton_cohomology_one_kummerSeqOpen_X₂ (U : OpenSubgroup Gal(Ksep/K)) :
    Subsingleton (cohomology (kummerSeqOpen (K := K) (Ksep := Ksep) n (U : Subgroup Gal(Ksep/K))).X₂ 1) :=
  (ModuleCat.isZero_iff_subsingleton).1 ((localClassFormationOfIsSepClosure K Ksep).isZero_H1_open_subgroups U)

variable {K Ksep}

theorem injective_cohomologyMap_kummerSeqOpen_f_two (hn : (n : K) ≠ 0)
    (U : OpenSubgroup Gal(Ksep/K)) :
    Function.Injective
      (cohomologyMap (kummerSeqOpen (K := K) (Ksep := Ksep) n (U : Subgroup Gal(Ksep/K))).f 2).hom :=
  cohomologyMap_f_injective_of_subsingleton (kummerSeqOpen_shortExact hn _) 1
    (subsingleton_cohomology_one_kummerSeqOpen_X₂ K Ksep (n := n) U)

noncomputable def rootsOfUnityInv (n : ℕ) (U : OpenSubgroup Gal(Ksep/K)) :
    cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 2 →+ QZ :=
  ((localClassFormationOfIsSepClosure K Ksep).inv U).comp
    (cohomologyMap (kummerSeqOpen (K := K) (Ksep := Ksep) n (U : Subgroup Gal(Ksep/K))).f 2).hom.toAddMonoidHom

theorem rootsOfUnityInv_apply (n : ℕ) (U : OpenSubgroup Gal(Ksep/K))
    (x : cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 2) :
    rootsOfUnityInv n U x = (localClassFormationOfIsSepClosure K Ksep).inv U
      ((cohomologyMap (kummerSeqOpen (K := K) (Ksep := Ksep) n (U : Subgroup Gal(Ksep/K))).f 2).hom x) :=
  rfl

theorem rootsOfUnityInv_injective (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    Function.Injective (rootsOfUnityInv (Ksep := Ksep) n U) :=
  ((localClassFormationOfIsSepClosure K Ksep).inv_bijective U).1.comp
    (injective_cohomologyMap_kummerSeqOpen_f_two hn U)

theorem range_rootsOfUnityInv (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    (rootsOfUnityInv (Ksep := Ksep) n U).range = (zmodToQZ n).range := by
  have : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  set F := localClassFormationOfIsSepClosure K Ksep
  set S := kummerSeqOpen (K := K) (Ksep := Ksep) n (U : Subgroup Gal(Ksep/K))
  have hS : S.ShortExact := kummerSeqOpen_shortExact hn _
  ext q
  simp only [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    refine exists_zmodToQZ_eq ?_
    have h0 : n • (cohomologyMap S.f 2).hom x = 0 := by
      rw [← cohomologyMap_kummerSeqOpen_g_apply n (U : Subgroup Gal(Ksep/K)) 2]
      exact cohomologyMap_g_cohomologyMap_f_apply (S := S) 2 x
    calc n • rootsOfUnityInv n U x = F.inv U (n • (cohomologyMap S.f 2).hom x) :=
          (map_nsmul (F.inv U) n ((cohomologyMap S.f 2).hom x)).symm
      _ = 0 := by rw [h0]; exact (F.inv U).map_zero
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := (F.inv_bijective U).2 (zmodToQZ n a)
    have hny : n • y = 0 := by
      apply (F.inv_bijective U).1
      rw [map_nsmul, hy, ← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul,
        map_zero, map_zero]
    obtain ⟨x, hx⟩ := exists_cohomologyMap_f_eq hS 2 y
      ((cohomologyMap_kummerSeqOpen_g_apply n _ 2 y).trans hny)
    exact ⟨x, show F.inv U ((cohomologyMap S.f 2).hom x) = _ by rw [hx, hy]⟩

noncomputable def localInvRootsOfUnity (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 2 ≃+
      ZMod n :=
  haveI : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  (AddMonoidHom.ofInjective (rootsOfUnityInv_injective hn U)).trans
    ((AddEquiv.addSubgroupCongr (range_rootsOfUnityInv hn U)).trans
      (AddMonoidHom.ofInjective (zmodToQZ_injective (n := n))).symm)

theorem zmodToQZ_localInvRootsOfUnity (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (x : cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 2) :
    zmodToQZ n (localInvRootsOfUnity hn U x) = rootsOfUnityInv n U x := by
  have : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  set w := AddEquiv.addSubgroupCongr (range_rootsOfUnityInv hn U)
    (AddMonoidHom.ofInjective (rootsOfUnityInv_injective hn U) x) with hw
  have h1 : (w : QZ) = rootsOfUnityInv n U x :=
    AddMonoidHom.ofInjective_apply (rootsOfUnityInv_injective hn U) (x := x)
  have h2 := AddMonoidHom.ofInjective_apply (zmodToQZ_injective (n := n))
    (x := (AddMonoidHom.ofInjective (zmodToQZ_injective (n := n))).symm w)
  rw [AddEquiv.apply_symm_apply] at h2
  exact h2.symm.trans h1

theorem localInvRootsOfUnity_cores (hn : (n : K) ≠ 0) (U V : OpenSubgroup Gal(Ksep/K)) (h : V ≤ U)
    (x : cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 2) :
    localInvRootsOfUnity hn U (cohomologyCoresLE (galRootsOfUnity.{0} K Ksep n) h 2 x) =
      localInvRootsOfUnity hn V x := by
  have : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  apply zmodToQZ_injective
  rw [zmodToQZ_localInvRootsOfUnity, zmodToQZ_localInvRootsOfUnity]
  exact (congrArg ((localClassFormationOfIsSepClosure K Ksep).inv U)
      (cohomologyCoresLE_cohomologyMap (kummerSequence K Ksep n).f h 2 x).symm).trans
    (ClassFormation.inv_cohomologyCoresLE _ h _)

end Local

end GroundTheory.ProfCoh
