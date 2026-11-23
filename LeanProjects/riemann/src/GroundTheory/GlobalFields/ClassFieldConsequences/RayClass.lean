import Mathlib
import GroundTheory.GlobalFields.ClassFieldConsequences.CongruenceSubgroupLeStandardOpenSubgroup

open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace Modulus

variable (𝔪 : Modulus K)

def rayGroup : Subgroup (IdeleGroup K) :=
  (diagonal K).range ⊔ 𝔪.congruenceSubgroup

abbrev RayClassGroup : Type _ :=
  IdeleGroup K ⧸ 𝔪.rayGroup

theorem diagonal_range_le_rayGroup : (diagonal K).range ≤ 𝔪.rayGroup :=
  le_sup_left

theorem congruenceSubgroup_le_rayGroup : 𝔪.congruenceSubgroup ≤ 𝔪.rayGroup :=
  le_sup_right

theorem map_rayGroup :
    𝔪.rayGroup.map (QuotientGroup.mk' (diagonal K).range) =
      𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) := by
  rw [rayGroup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  rfl

instance : (𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K)).Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩

def quotientMapCongruenceEquiv :
    IdeleClassGroup K ⧸ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≃* 𝔪.RayClassGroup :=
  (QuotientGroup.quotientMulEquivOfEq 𝔪.map_rayGroup.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ 𝔪.diagonal_range_le_rayGroup)

@[simp]
theorem quotientMapCongruenceEquiv_mk (x : IdeleGroup K) :
    𝔪.quotientMapCongruenceEquiv (QuotientGroup.mk (IdeleClassGroup.mk K x)) =
      (QuotientGroup.mk x : 𝔪.RayClassGroup) :=
  rfl

theorem map_idealLevel_sup_le :
    (idealLevel 𝔪.ideal).map ofFinite ⊔ (infinitePositive K).map ofInfinite ≤
      𝔪.congruenceSubgroup := by
  refine sup_le ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    refine 𝔪.mem_congruenceSubgroup.2 ⟨fun v ↦ ?_, fun w _ ↦ ?_⟩
    · rw [← finiteComponent_toFinite, toFinite_ofFinite]
      exact mem_finiteLevel.1 hy v
    · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        ((toInfinite K (ofFinite y) : InfiniteAdeleRing K) w.1)
      rw [toInfinite_ofFinite]
      change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (1 : w.1.Completion)
      rw [map_one]
      exact one_pos
  · rintro _ ⟨z, hz, rfl⟩
    refine 𝔪.mem_congruenceSubgroup.2 ⟨fun v ↦ ?_, fun w _ ↦ ?_⟩
    · rw [← finiteComponent_toFinite, toFinite_ofInfinite, map_one]
      exact one_mem _
    · have h : ((infiniteProj w.1 (ofInfinite z) : (w.1.Completion)ˣ) : w.1.Completion) =
          (toInfinite K (ofInfinite z) : InfiniteAdeleRing K) w.1 := rfl
      rw [h, toInfinite_ofInfinite]
      exact hz w.1 w.2

theorem congruenceSubgroup_eq_sup (h : 𝔪.real = Set.univ) :
    𝔪.congruenceSubgroup =
      (idealLevel 𝔪.ideal).map ofFinite ⊔ (infinitePositive K).map ofInfinite := by
  refine le_antisymm (fun x hx ↦ ?_) 𝔪.map_idealLevel_sup_le
  obtain ⟨hf, hi⟩ := 𝔪.mem_congruenceSubgroup.1 hx
  rw [← ofFinite_mul_ofInfinite x]
  refine mul_mem (Subgroup.mem_sup_left ⟨_, mem_finiteLevel.2 fun v ↦ ?_, rfl⟩)
    (Subgroup.mem_sup_right ⟨_, fun w hw ↦ hi ⟨w, hw⟩ (h ▸ Set.mem_univ _), rfl⟩)
  rw [finiteComponent_toFinite]
  exact hf v

theorem rayGroup_ideal_le : IdeleGroup.rayGroup K 𝔪.ideal ≤ 𝔪.rayGroup := by
  rw [IdeleGroup.rayGroup, sup_assoc]
  exact sup_le_sup_left 𝔪.map_idealLevel_sup_le _

theorem rayGroup_eq (h : 𝔪.real = Set.univ) : 𝔪.rayGroup = IdeleGroup.rayGroup K 𝔪.ideal := by
  rw [IdeleGroup.rayGroup, sup_assoc, rayGroup, 𝔪.congruenceSubgroup_eq_sup h]

def rayClassGroupEquiv_of_real_eq_univ (h : 𝔪.real = Set.univ) :
    𝔪.RayClassGroup ≃* _root_.GroundTheory.Global.RayClassGroup K 𝔪.ideal :=
  QuotientGroup.quotientMulEquivOfEq (𝔪.rayGroup_eq h)

@[simp]
theorem rayClassGroupEquiv_of_real_eq_univ_mk (h : 𝔪.real = Set.univ) (x : IdeleGroup K) :
    𝔪.rayClassGroupEquiv_of_real_eq_univ h (QuotientGroup.mk x) =
      (QuotientGroup.mk x : _root_.GroundTheory.Global.RayClassGroup K 𝔪.ideal) :=
  rfl

theorem RayClassGroup.finite : Finite 𝔪.RayClassGroup := by
  have : Finite (_root_.GroundTheory.Global.RayClassGroup K 𝔪.ideal) :=
    _root_.GroundTheory.Global.RayClassGroup.finite 𝔪.ideal_ne_bot
  have : (IdeleGroup.rayGroup K 𝔪.ideal).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : 𝔪.rayGroup.FiniteIndex := Subgroup.finiteIndex_of_le 𝔪.rayGroup_ideal_le
  exact Subgroup.finite_quotient_of_finiteIndex

instance : Finite 𝔪.RayClassGroup :=
  RayClassGroup.finite 𝔪

theorem finiteIndex_map_congruenceSubgroup :
    (𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K)).FiniteIndex := by
  have : Finite (IdeleClassGroup K ⧸ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K)) :=
    Finite.of_equiv _ 𝔪.quotientMapCongruenceEquiv.symm.toEquiv
  exact Subgroup.finiteIndex_of_finite_quotient

end Modulus

end

end GroundTheory.Global
