import Mathlib
import GroundTheory.ProfiniteCohomology.ClassFormations.Quotient
import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
import GroundTheory.ProfiniteCohomology.InflationRestriction.Higher
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

namespace QZ

theorem cyclic_of_injective {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (Φ : X →+ Y)
    (hΦ : Function.Injective Φ) (inv : Y →+ QZ) (hinv : Function.Injective inv) {n : ℕ}
    (hn : 0 < n) (hker : ∀ x, n • inv (Φ x) = 0) (e : X) (he : inv (Φ e) = mk (1 / n)) :
    addOrderOf e = n ∧ ∀ x, ∃ m : ℤ, x = m • e := by
  have hι : Function.Injective (inv.comp Φ) := hinv.comp hΦ
  refine ⟨?_, fun x => ?_⟩
  · rw [← addOrderOf_injective (inv.comp Φ) hι e, AddMonoidHom.comp_apply, he,
      addOrderOf_mk_one_div hn]
  · obtain ⟨m, hm⟩ := exists_eq_nsmul_mk_one_div hn (hker x)
    refine ⟨m, hι ?_⟩
    rw [map_zsmul, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, he, hm, natCast_zsmul]

theorem nsmul_mk_one_div_mul {a b : ℕ} (ha : a ≠ 0) : a • mk (1 / (a * b : ℕ)) = mk (1 / b) := by
  rw [← mk_nsmul, nsmul_eq_mul]
  congr 1
  push_cast
  field_simp

end QZ

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem compactSpace_of_isOpen [CompactSpace G] {W : Subgroup G} (hW : IsOpen (W : Set G)) :
    CompactSpace W :=
  isCompact_iff_compactSpace.mp (W.isClosed_of_isOpen hW).isCompact

section InfRes

variable [CompactSpace G] [TotallyDisconnectedSpace G]
  (A : Rep.{u} k G) [IsDiscreteRep A] {U V : Subgroup G} (hU : IsOpen (U : Set G))
  (hV : IsOpen (V : Set G)) (hVU : V ≤ U) [(V.subgroupOf U).Normal]

omit [CompactSpace G] [TotallyDisconnectedSpace G] [(V.subgroupOf U).Normal] in
include hVU in

theorem isZero_H1_subgroupOf (h1 : IsZero (cohomology (Rep.res V.subtype A) 1)) :
    IsZero (cohomology (Rep.res (V.subgroupOf U).subtype (Rep.res U.subtype A)) 1) :=
  h1.of_iso (asIso (cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe hVU).symm.toMonoidHom
    (continuous_subgroupOfEquivOfLe_symm hVU) (resSubgroupOfHom hVU A) 1))

include hU hV hVU in

theorem cohomologyInfl_two_injective_of_open (h1 : IsZero (cohomology (Rep.res V.subtype A) 1)) :
    Function.Injective (cohomologyInfl (Rep.res U.subtype A) (V.subgroupOf U) 2).hom := by
  have := compactSpace_of_isOpen hU
  exact cohomologyInfl_injective (Subgroup.isClosed_of_isOpen _ (isOpen_subgroupOf hV U))
    two_ne_zero fun i hi hi2 => by
      obtain rfl : i = 1 := by omega
      exact isZero_H1_subgroupOf A hVU h1

include hU hV in

theorem mem_range_cohomologyInfl_two_iff (h1 : IsZero (cohomology (Rep.res V.subtype A) 1))
    (x : cohomology (Rep.res U.subtype A) 2) :
    (∃ y, (cohomologyInfl (Rep.res U.subtype A) (V.subgroupOf U) 2).hom y = x) ↔
      (cohomologyResLE A hVU 2).hom x = 0 := by
  rw [cohomologyResLE_apply_eq_zero_iff]
  constructor
  · rintro ⟨y, rfl⟩
    rw [← ModuleCat.comp_apply, cohomologyInfl_comp_cohomologyRes _ _ 1]
    rfl
  · intro hx
    have := compactSpace_of_isOpen hU
    have hx' : x ∈ LinearMap.ker (cohomologyRes (Rep.res U.subtype A) (V.subgroupOf U) 2).hom := hx
    rw [← range_cohomologyInfl_eq_ker_cohomologyRes
      (Subgroup.isClosed_of_isOpen _ (isOpen_subgroupOf hV U)) two_ne_zero fun i hi hi2 => by
        obtain rfl : i = 1 := by omega
        exact isZero_H1_subgroupOf A hVU h1] at hx'
    exact hx'

end InfRes

theorem relIndex_ne_zero_of_isOpen [CompactSpace G] {V : Subgroup G} (hV : IsOpen (V : Set G))
    (U : Subgroup G) : V.relIndex U ≠ 0 := by
  have := Subgroup.quotient_finite_of_isOpen V hV
  have := Subgroup.finiteIndex_of_finite_quotient (H := V)
  have := Subgroup.isFiniteRelIndex_of_finiteIndex (H := V) (K := U)
  exact Subgroup.relIndex_ne_zero

def quotPreimageOpen {U V : OpenSubgroup G} [((V : Subgroup G).subgroupOf U).Normal]
    (hVU : V ≤ U) (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U)) : OpenSubgroup G where
  toSubgroup := quotPreimage (U : Subgroup G) V S
  isOpen' := Subgroup.isOpen_mono (le_quotPreimage (show (V : Subgroup G) ≤ U from hVU) S) V.isOpen

instance normal_subgroupOf_quotPreimageOpen {U V : OpenSubgroup G}
    [((V : Subgroup G).subgroupOf U).Normal] (hVU : V ≤ U)
    (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U)) :
    ((V : Subgroup G).subgroupOf (quotPreimageOpen hVU S : Subgroup G)).Normal :=
  normal_subgroupOf_quotPreimage S

namespace PreClassFormation

variable [CompactSpace G] [TotallyDisconnectedSpace G]
  {C : Rep.{u} k G} [IsDiscreteRep C] (F : PreClassFormation C)
  {U V : OpenSubgroup G} (hVU : V ≤ U) [((V : Subgroup G).subgroupOf U).Normal]

include F

theorem mem_range_cohomologyInfl_two_iff (x : H2Open C U) :
    (∃ y, (cohomologyInfl (Rep.res (U : Subgroup G).subtype C)
        ((V : Subgroup G).subgroupOf U) 2).hom y = x) ↔
      (cohomologyResLE C (show (V : Subgroup G) ≤ U from hVU) 2).hom x = 0 :=
  GroundTheory.ProfCoh.mem_range_cohomologyInfl_two_iff C U.isOpen V.isOpen hVU (F.isZero_H1_open_subgroups V) x

include hVU in

theorem inv_cohomologyInfl_fundamentalClass (hVinj : Function.Injective (F.inv V))
    (hex : ∃ x : H2Open C U, F.inv U x = QZ.mk (1 / ((V : Subgroup G).relIndex U : ℚ))) :
    F.inv U ((cohomologyInfl (Rep.res (U : Subgroup G).subtype C)
        ((V : Subgroup G).subgroupOf U) 2).hom (F.fundamentalClass U V)) =
      QZ.mk (1 / ((V : Subgroup G).relIndex U : ℚ)) := by
  obtain ⟨x, hx⟩ := hex
  have hres : (cohomologyResLE C (show (V : Subgroup G) ≤ U from hVU) 2).hom x = 0 :=
    (F.resLE_eq_zero_iff hVU hVinj x).2 (by rw [hx]; exact QZ.nsmul_mk_one_div _)
  obtain ⟨y, hy⟩ := (F.mem_range_cohomologyInfl_two_iff hVU x).2 hres
  have : Nonempty (H2Quotient C U V) := ⟨0⟩
  exact Function.invFun_eq (f := fun y : H2Quotient C U V => F.inv U ((cohomologyInfl
    (Rep.res (U : Subgroup G).subtype C) ((V : Subgroup G).subgroupOf U) 2).hom y))
    ⟨y, by simp only [hy, hx]⟩

section Subgroup

variable (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U))

omit [CompactSpace G] [TotallyDisconnectedSpace G] F in
include hVU in

theorem cohomologyInflQuot_one_injective : Function.Injective (cohomologyInflQuot C S 1).hom := by
  rw [cohomologyInflQuot_eq C (show (V : Subgroup G) ≤ U from hVU) S 1, ModuleCat.hom_comp]
  have := isIso_cohomologyMapAlong_quotPreimageEquiv C V.isOpen
    (show (V : Subgroup G) ≤ U from hVU) S 1
  exact (cohomologyInfl_one_injective _ _).comp ((ModuleCat.mono_iff_injective _).1 inferInstance)

include hVU in

theorem cohomologyInflQuot_two_injective : Function.Injective (cohomologyInflQuot C S 2).hom := by
  have hVW : (V : Subgroup G) ≤ quotPreimageOpen hVU S :=
    le_quotPreimage (show (V : Subgroup G) ≤ U from hVU) S
  rw [cohomologyInflQuot_eq C (show (V : Subgroup G) ≤ U from hVU) S 2, ModuleCat.hom_comp]
  have := isIso_cohomologyMapAlong_quotPreimageEquiv C V.isOpen
    (show (V : Subgroup G) ≤ U from hVU) S 2
  exact (cohomologyInfl_two_injective_of_open C (quotPreimageOpen hVU S).isOpen V.isOpen hVW
    (F.isZero_H1_open_subgroups V)).comp ((ModuleCat.mono_iff_injective _).1 inferInstance)

theorem resLE_cohomologyInflQuot (y) :
    (cohomologyResLE C (le_quotPreimage (show (V : Subgroup G) ≤ U from hVU) S) 2).hom
      ((cohomologyInflQuot C S 2).hom y) = 0 := by
  have hVW : (V : Subgroup G) ≤ quotPreimageOpen hVU S :=
    le_quotPreimage (show (V : Subgroup G) ≤ U from hVU) S
  refine (GroundTheory.ProfCoh.mem_range_cohomologyInfl_two_iff C (quotPreimageOpen hVU S).isOpen V.isOpen
    hVW (F.isZero_H1_open_subgroups V) _).1 ?_
  rw [cohomologyInflQuot_eq C (show (V : Subgroup G) ≤ U from hVU) S 2, ModuleCat.hom_comp]
  exact ⟨_, rfl⟩

omit [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem inv_cohomologyInflQuot_cohomologyRes (z : H2Quotient C U V) :
    F.inv (quotPreimageOpen hVU S) ((cohomologyInflQuot C S 2).hom
        ((cohomologyRes ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
          ((V : Subgroup G).subgroupOf U)) S 2).hom z)) =
      ((quotPreimageOpen hVU S : Subgroup G).relIndex U) •
        F.inv U ((cohomologyInfl (Rep.res (U : Subgroup G).subtype C)
          ((V : Subgroup G).subgroupOf U) 2).hom z) := by
  have h := congrArg (fun φ => φ.hom z) (cohomologyRes_comp_cohomologyInflQuot C S 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  exact F.inv_res U (quotPreimageOpen hVU S) (quotPreimage_le S) _

include hVU in

theorem inv_cohomologyInflQuot_cohomologyRes_fundamentalClass
    (hVinj : Function.Injective (F.inv V))
    (hex : ∃ x : H2Open C U, F.inv U x = QZ.mk (1 / ((V : Subgroup G).relIndex U : ℚ))) :
    F.inv (quotPreimageOpen hVU S) ((cohomologyInflQuot C S 2).hom
        ((cohomologyRes ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
          ((V : Subgroup G).subgroupOf U)) S 2).hom (F.fundamentalClass U V))) =
      QZ.mk (1 / ((V : Subgroup G).relIndex (quotPreimageOpen hVU S : Subgroup G) : ℚ)) := by
  have hVW : V ≤ quotPreimageOpen hVU S :=
    le_quotPreimage (show (V : Subgroup G) ≤ U from hVU) S
  have hidx : (V : Subgroup G).relIndex U =
      (quotPreimageOpen hVU S : Subgroup G).relIndex U *
        (V : Subgroup G).relIndex (quotPreimageOpen hVU S : Subgroup G) := by
    rw [mul_comm]
    exact (Subgroup.relIndex_mul_relIndex _ _ _ hVW (quotPreimage_le S)).symm
  rw [F.inv_cohomologyInflQuot_cohomologyRes hVU S, F.inv_cohomologyInfl_fundamentalClass hVU
    hVinj hex, hidx, QZ.nsmul_mk_one_div_mul (relIndex_ne_zero_of_isOpen
      (quotPreimageOpen hVU S).isOpen _)]

include hVU in

theorem cyclic_cohomologyRes_fundamentalClass (hinj : ∀ W : OpenSubgroup G, Function.Injective (F.inv W))
    (hex : ∃ x : H2Open C U, F.inv U x = QZ.mk (1 / ((V : Subgroup G).relIndex U : ℚ))) :
    addOrderOf ((cohomologyRes ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
        ((V : Subgroup G).subgroupOf U)) S 2).hom (F.fundamentalClass U V)) = Nat.card S ∧
      ∀ y, ∃ m : ℤ, y = m • (cohomologyRes ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
        ((V : Subgroup G).subgroupOf U)) S 2).hom (F.fundamentalClass U V) := by
  have hVW : V ≤ quotPreimageOpen hVU S :=
    le_quotPreimage (show (V : Subgroup G) ≤ U from hVU) S
  have hcard : (V : Subgroup G).relIndex (quotPreimageOpen hVU S : Subgroup G) = Nat.card S :=
    relIndex_quotPreimage S
  refine QZ.cyclic_of_injective (cohomologyInflQuot C S 2).hom.toAddMonoidHom
    (F.cohomologyInflQuot_two_injective hVU S) (F.inv (quotPreimageOpen hVU S))
    (hinj _) (hcard ▸ Nat.pos_of_ne_zero (relIndex_ne_zero_of_isOpen V.isOpen _)) (fun y => ?_) _ ?_
  · rw [← hcard]
    exact (F.resLE_eq_zero_iff hVW (hinj V) _).1 (F.resLE_cohomologyInflQuot hVU S y)
  · change F.inv (quotPreimageOpen hVU S) ((cohomologyInflQuot C S 2).hom _) = _
    rw [F.inv_cohomologyInflQuot_cohomologyRes_fundamentalClass hVU S (hinj V) hex, hcard]

end Subgroup

noncomputable def groupFundamentalClass (U V : OpenSubgroup G)
    [((V : Subgroup G).subgroupOf U).Normal] :
    groupCohomology ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
      ((V : Subgroup G).subgroupOf U)) 2 :=
  (cohomologyToGroupCohomology _ 2).hom (F.fundamentalClass U V)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem groupCohomology_map_groupFundamentalClass
    (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U)) :
    (groupCohomology.map S.subtype (𝟙 _) 2).hom (F.groupFundamentalClass U V) =
      (cohomologyToGroupCohomology _ 2).hom
        ((cohomologyRes ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
          ((V : Subgroup G).subgroupOf U)) S 2).hom (F.fundamentalClass U V)) := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ (F.fundamentalClass U V))
    (cohomologyRes_comp_homologyMap_cochainsComplexι
      ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants ((V : Subgroup G).subgroupOf U))
      S 2)
  exact h.symm

include hVU in

theorem tate_hypotheses (hinj : ∀ W : OpenSubgroup G, Function.Injective (F.inv W))
    (hex : ∃ x : H2Open C U, F.inv U x = QZ.mk (1 / ((V : Subgroup G).relIndex U : ℚ)))
    (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U)) :
    IsZero (groupCohomology (Rep.res S.subtype ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
        ((V : Subgroup G).subgroupOf U))) 1) ∧
      addOrderOf ((groupCohomology.map S.subtype (𝟙 _) 2).hom (F.groupFundamentalClass U V)) =
        Nat.card S ∧
      ∀ y, ∃ m : ℤ, y = m • (groupCohomology.map S.subtype (𝟙 _) 2).hom (F.groupFundamentalClass U V) := by
  have := discreteTopology_quot (U := (U : Subgroup G)) V.isOpen
  refine ⟨?_, ?_, ?_⟩
  · refine IsZero.of_iso ?_ (cohomologyIsoGroupCohomology _ 1).symm
    have : Subsingleton (cohomology (Rep.res (quotPreimage (U : Subgroup G) V S).subtype C) 1) :=
      ModuleCat.subsingleton_of_isZero (F.isZero_H1_open_subgroups (quotPreimageOpen hVU S))
    have : Subsingleton (cohomology (Rep.res S.subtype ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
        ((V : Subgroup G).subgroupOf U))) 1) :=
      (cohomologyInflQuot_one_injective hVU S).subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  · have hinj' : Function.Injective (cohomologyIsoGroupCohomology (Rep.res S.subtype
        ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
          ((V : Subgroup G).subgroupOf U))) 2).hom.hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    rw [groupCohomology_map_groupFundamentalClass, ← cohomologyIsoGroupCohomology_hom]
    exact (addOrderOf_injective (cohomologyIsoGroupCohomology (Rep.res S.subtype
        ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
          ((V : Subgroup G).subgroupOf U))) 2).hom.hom.toAddMonoidHom hinj' _).trans
      (F.cyclic_cohomologyRes_fundamentalClass hVU S hinj hex).1
  · intro y
    obtain ⟨m, hm⟩ := (F.cyclic_cohomologyRes_fundamentalClass hVU S hinj hex).2
      ((cohomologyIsoGroupCohomology _ 2).inv.hom y)
    refine ⟨m, ?_⟩
    rw [groupCohomology_map_groupFundamentalClass, ← cohomologyIsoGroupCohomology_hom, ← map_zsmul,
      ← hm]
    exact (ModuleCat.hom_inv_apply (cohomologyIsoGroupCohomology _ 2) y).symm

end PreClassFormation

end GroundTheory.ProfCoh
