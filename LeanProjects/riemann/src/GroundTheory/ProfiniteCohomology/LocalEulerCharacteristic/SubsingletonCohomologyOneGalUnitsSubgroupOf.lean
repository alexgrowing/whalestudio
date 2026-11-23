import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.ConjAction
import GroundTheory.ProfiniteCohomology.ClassFormations.Corestriction
import GroundTheory.ProfiniteCohomology.LocalClassFormationAlt
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

section Formation

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {C : Rep.{u} k G} [IsDiscreteRep C]

omit [CompactSpace G] in

theorem cohomologyRes_subgroupOf_surjective {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ)
    (hs : Function.Surjective (cohomologyResLE C (show (V : Subgroup G) ≤ U from h) n).hom) :
    Function.Surjective
      (cohomologyRes (Rep.res (U : Subgroup G).subtype C) ((V : Subgroup G).subgroupOf U) n).hom := by
  intro y
  set e := cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from h)).symm.toMonoidHom
    (continuous_subgroupOfEquivOfLe_symm _) (resSubgroupOfHom (show (V : Subgroup G) ≤ U from h) C) n
  have he : Function.Injective e.hom := (ModuleCat.mono_iff_injective _).1 inferInstance
  obtain ⟨x, hx⟩ := hs (e.hom y)
  refine ⟨x, he ?_⟩
  rw [← hx, cohomologyResLE_eq_cohomologyRes_comp]
  rfl

theorem ClassFormation.cohomologyConj_two_eq_id (F : ClassFormation C) {U V : OpenSubgroup G}
    (h : V ≤ U) [((V : Subgroup G).subgroupOf (U : Subgroup G)).Normal] (g : (U : Subgroup G)) :
    cohomologyConj (Rep.res (U : Subgroup G).subtype C) ((V : Subgroup G).subgroupOf U) 2 g = 𝟙 _ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  obtain ⟨x, rfl⟩ := cohomologyRes_subgroupOf_surjective h 2 (F.cohomologyResLE_surjective h) y
  exact congrArg (fun φ => φ.hom x) (cohomologyRes_comp_cohomologyConj (Rep.res (U : Subgroup G).subtype C)
    ((V : Subgroup G).subgroupOf U) 2 g)

end Formation

section Local

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {l : ℕ}

noncomputable abbrev kummerSequenceResRes (l : ℕ) (U : Subgroup Gal(Ksep/K)) (N : Subgroup U) :
    ShortComplex (Rep (ULift.{0} ℤ) N) :=
  ((kummerSequence K Ksep l).map (Rep.resFunctor U.subtype)).map (Rep.resFunctor N.subtype)

instance isDiscreteRep_kummerSequenceResRes_X₁ (l : ℕ) (U : Subgroup Gal(Ksep/K)) (N : Subgroup U) :
    IsDiscreteRep (kummerSequenceResRes (K := K) (Ksep := Ksep) l U N).X₁ :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_kummerSequenceResRes_X₂ (l : ℕ) (U : Subgroup Gal(Ksep/K)) (N : Subgroup U) :
    IsDiscreteRep (kummerSequenceResRes (K := K) (Ksep := Ksep) l U N).X₂ :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_kummerSequenceResRes_X₃ (l : ℕ) (U : Subgroup Gal(Ksep/K)) (N : Subgroup U) :
    IsDiscreteRep (kummerSequenceResRes (K := K) (Ksep := Ksep) l U N).X₃ :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_res_res_galRootsOfUnity (U : Subgroup Gal(Ksep/K)) :
    IsDiscreteRep (Rep.res U.subtype (galRootsOfUnity.{0} K Ksep l)) :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_res_res_galUnits (U : Subgroup Gal(Ksep/K)) :
    IsDiscreteRep (Rep.res U.subtype (galUnits.{0} K Ksep)) :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_res_res_res_galUnits (U : Subgroup Gal(Ksep/K)) (N : Subgroup U) :
    IsDiscreteRep (Rep.res N.subtype (Rep.res U.subtype (galUnits.{0} K Ksep))) :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_res_res_res_galRootsOfUnity (U : Subgroup Gal(Ksep/K)) (N : Subgroup U) :
    IsDiscreteRep (Rep.res N.subtype (Rep.res U.subtype (galRootsOfUnity.{0} K Ksep l))) :=
  isDiscreteRep_res_subtype _ _

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem kummerSequenceResRes_shortExact (hl : (l : K) ≠ 0) (U : Subgroup Gal(Ksep/K)) (N : Subgroup U) :
    (kummerSequenceResRes (K := K) (Ksep := Ksep) l U N).ShortExact :=
  shortExact_map_res N (shortExact_map_res U (kummerSequence_shortExact l hl))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem subsingleton_cohomology_one_galUnits_subgroupOf {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U) :
    Subsingleton (cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf U).subtype
      (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep))) 1) := by
  have e := asIso (cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe
    (show (V : Subgroup Gal(Ksep/K)) ≤ U from h)).symm.toMonoidHom
    (continuous_subgroupOfEquivOfLe_symm _) (resSubgroupOfHom _ (galUnits.{0} K Ksep)) 1)
  exact (ModuleCat.isZero_iff_subsingleton).1 ((isZero_H1_open K Ksep V).of_iso e)

theorem cohomologyConj_two_galRootsOfUnity_eq_id (hl : (l : K) ≠ 0) {U V : OpenSubgroup Gal(Ksep/K)}
    (h : V ≤ U) [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal] (g : (U : Subgroup Gal(Ksep/K))) :
    cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))
      ((V : Subgroup Gal(Ksep/K)).subgroupOf U) 2 g = 𝟙 _ := by
  set N := (V : Subgroup Gal(Ksep/K)).subgroupOf U
  set f := (Rep.resFunctor (U : Subgroup Gal(Ksep/K)).subtype).map (kummerSequence K Ksep l).f
  set fN := cohomologyMap ((Rep.resFunctor N.subtype).map f) 2
  have hinj : Function.Injective fN.hom :=
    cohomologyMap_f_injective_of_subsingleton (kummerSequenceResRes_shortExact hl _ N) 1
      (subsingleton_cohomology_one_galUnits_subgroupOf h)
  have hnat := cohomologyConj_naturality (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
    (galRootsOfUnity.{0} K Ksep l)) N f 2 g
  refine ModuleCat.hom_ext (LinearMap.ext fun y => hinj ?_)
  have e1 : (cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)) N 2 g).hom
      (fN.hom y) = fN.hom ((cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep l)) N 2 g).hom y) :=
    congrArg (fun φ => φ.hom y) hnat
  have e2 := congrArg (fun φ => φ.hom (fN.hom y))
    ((localClassFormationOfIsSepClosure K Ksep).cohomologyConj_two_eq_id h g)
  exact e1.symm.trans (e2.trans rfl)

end Local

end GroundTheory.ProfCoh
