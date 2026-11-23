import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.SubsingletonCohomologyOneGalUnitsSubgroupOf
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CohomologyKummer
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CohomologyGal
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.KummerOpen
import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {l : ℕ} (hl : (l : K) ≠ 0)

section Open

noncomputable def rootsOfUnityTwoInv (l : ℕ) (V : OpenSubgroup Gal(Ksep/K)) :
    cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l)) 2 →+ QZ :=
  ((localClassFormationOfIsSepClosure K Ksep).inv V).comp
    (cohomologyMap (kummerSequenceRes (K := K) (Ksep := Ksep) l (V : Subgroup Gal(Ksep/K))).f 2).hom.toAddMonoidHom

theorem rootsOfUnityTwoInv_apply (V : OpenSubgroup Gal(Ksep/K))
    (x : cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l)) 2) :
    rootsOfUnityTwoInv l V x = (localClassFormationOfIsSepClosure K Ksep).inv V
      ((cohomologyMap (kummerSequenceRes (K := K) (Ksep := Ksep) l (V : Subgroup Gal(Ksep/K))).f 2).hom x) :=
  AddMonoidHom.comp_apply _ _ x

include hl in

theorem rootsOfUnityTwoInv_injective (V : OpenSubgroup Gal(Ksep/K)) :
    Function.Injective (rootsOfUnityTwoInv (K := K) (Ksep := Ksep) l V) :=
  ((localClassFormationOfIsSepClosure K Ksep).inv_bijective V).1.comp
    (cohomologyMap_f_injective_of_subsingleton
      (kummerSequenceRes_shortExact (Ksep := Ksep) l (V : Subgroup Gal(Ksep/K)) hl) 1
      (subsingleton_cohomology_one_galUnits_open K Ksep V))

include hl in

theorem range_rootsOfUnityTwoInv (V : OpenSubgroup Gal(Ksep/K)) :
    (rootsOfUnityTwoInv (K := K) (Ksep := Ksep) l V).range = (zmodToQZ l).range := by
  have : NeZero l := ⟨by rintro rfl; exact hl Nat.cast_zero⟩
  set F := localClassFormationOfIsSepClosure K Ksep
  set S := kummerSequenceRes (K := K) (Ksep := Ksep) l (V : Subgroup Gal(Ksep/K))
  have hS : S.ShortExact := kummerSequenceRes_shortExact l _ hl
  ext q
  simp only [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    refine exists_zmodToQZ_eq ?_
    have e : l • (cohomologyMap S.f 2).hom x = 0 :=
      (cohomologyMap_kummerSequenceRes_g_apply l (V : Subgroup Gal(Ksep/K)) 2 _).symm.trans
        (cohomologyMap_g_cohomologyMap_f_apply (S := S) 2 x)
    rw [rootsOfUnityTwoInv_apply]
    exact (map_nsmul (F.inv V) l _).symm.trans ((congrArg (F.inv V) e).trans (map_zero _))
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := (F.inv_bijective V).2 (zmodToQZ l a)
    have hny : l • y = 0 := by
      apply (F.inv_bijective V).1
      rw [map_nsmul, hy, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero, map_zero]
    obtain ⟨x, hx⟩ := exists_cohomologyMap_f_eq hS 2 y
      ((cohomologyMap_kummerSequenceRes_g_apply l (V : Subgroup Gal(Ksep/K)) 2 y).trans hny)
    exact ⟨x, (rootsOfUnityTwoInv_apply V x).trans ((congrArg (F.inv V) hx).trans hy)⟩

noncomputable def rootsOfUnityTwoEquivOpen (V : OpenSubgroup Gal(Ksep/K)) :
    cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l)) 2 ≃+ ZMod l :=
  haveI : NeZero l := ⟨by rintro rfl; exact hl Nat.cast_zero⟩
  (AddMonoidHom.ofInjective (rootsOfUnityTwoInv_injective hl V)).trans
    ((AddEquiv.addSubgroupCongr (range_rootsOfUnityTwoInv hl V)).trans
      (AddMonoidHom.ofInjective (zmodToQZ_injective (n := l))).symm)

end Open

variable {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U)

noncomputable def cohomologyTwoRootsEquiv :
    cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 2 ≃+ ZMod l :=
  (asIso (cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe
      (show (V : Subgroup Gal(Ksep/K)) ≤ U from h)).symm.toMonoidHom
    (continuous_subgroupOfEquivOfLe_symm _) (resSubgroupOfHom _ (galRootsOfUnity.{0} K Ksep l)) 2)).toLinearEquiv.toAddEquiv.trans
    (rootsOfUnityTwoEquivOpen hl V)

variable [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]

theorem cohomologyTwoRootsEquiv_cohomologyConj (g : (U : Subgroup Gal(Ksep/K)))
    (x : cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 2) :
    cohomologyTwoRootsEquiv hl h ((cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep l)) ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) 2 g).hom x) =
      cohomologyTwoRootsEquiv hl h x := by
  rw [cohomologyConj_two_galRootsOfUnity_eq_id hl h g]
  rfl

end GroundTheory.ProfCoh
