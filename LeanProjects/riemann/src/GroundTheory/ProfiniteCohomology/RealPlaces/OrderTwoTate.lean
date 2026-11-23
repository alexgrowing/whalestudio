import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.OrderTwo
import GroundTheory.ProfiniteCohomology.RealPlaces.InvolutionDuality
import GroundTheory.ProfiniteCohomology.RealPlaces.LocalDualityDefs
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Involution

namespace OrderTwo

section Equivs

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] (A : Rep.{0} k G) [IsDiscreteRep A] {c : G}
  (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

abbrev act (A : Rep.{0} k G) (c : G) : A →+ A := (A.ρ c).toAddMonoidHom

omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] [IsDiscreteRep A] in
theorem mem_fixedSub_neg_act {α : A} : α ∈ fixedSub (-act A c) ↔ α + A.ρ c α = 0 := by
  rw [mem_fixedSub, AddMonoidHom.neg_apply, neg_eq_iff_add_eq_zero, add_comm]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] [IsDiscreteRep A] in
theorem mem_fixedSub_act {a : A} : a ∈ fixedSub (act A c) ↔ A.ρ c a = a :=
  mem_fixedSub

theorem cocycleOne_add (α β : A) (hα : α + A.ρ c α = 0) (hβ : β + A.ρ c β = 0)
    (hαβ : α + β + A.ρ c (α + β) = 0) :
    cocycleOne A hG hc (α + β) hαβ = cocycleOne A hG hc α hα + cocycleOne A hG hc β hβ := by
  apply cocycles_ext
  rw [map_add, cochainOf_add, cochainOf_cocycleOne, cochainOf_cocycleOne, cochainOf_cocycleOne]
  funext v
  simp only [cochainOne, Pi.add_apply]
  split_ifs <;> simp

theorem cocycleTwo_add (a b : A) (ha : A.ρ c a = a) (hb : A.ρ c b = b)
    (hab : A.ρ c (a + b) = a + b) :
    cocycleTwo A hG hc (a + b) hab = cocycleTwo A hG hc a ha + cocycleTwo A hG hc b hb := by
  apply cocycles_ext
  rw [map_add, cochainOf_add, cochainOf_cocycleTwo, cochainOf_cocycleTwo, cochainOf_cocycleTwo]
  funext v
  simp only [cochainTwo, Pi.add_apply]
  split_ifs <;> simp

def h1Hom : fixedSub (-act A c) →+ cohomology A 1 where
  toFun α := cohomologyπ A 1 (cocycleOne A hG hc α ((mem_fixedSub_neg_act A).1 α.2))
  map_zero' := by
    rw [← map_zero (cohomologyπ A 1).hom]
    congr 1
    apply cocycles_ext
    rw [cochainOf_cocycleOne, map_zero, cochainOf_zero]
    funext v
    simp [cochainOne]
  map_add' α β := by
    rw [← map_add]
    congr 1
    exact cocycleOne_add A hG hc _ _ _ _ _

theorem h1Hom_apply (α : fixedSub (-act A c)) :
    h1Hom A hG hc α = cohomologyπ A 1 (cocycleOne A hG hc α ((mem_fixedSub_neg_act A).1 α.2)) :=
  rfl

def h1EquivOfOrderTwo : tateQuot (-act A c) ≃+ cohomology A 1 :=
  AddEquiv.ofBijective (QuotientAddGroup.lift _ (h1Hom A hG hc) (by
      intro α hα
      rw [AddSubgroup.mem_addSubgroupOf, mem_traceSub] at hα
      obtain ⟨y, hy⟩ := hα
      rw [AddMonoidHom.mem_ker, h1Hom_apply, cohomologyπ_cocycleOne_eq_zero_iff]
      refine ⟨-y, ?_⟩
      rw [← hy, AddMonoidHom.neg_apply, map_neg]
      simp [sub_eq_add_neg, add_comm]))
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective x
      rw [QuotientAddGroup.lift_mk, h1Hom_apply, cohomologyπ_cocycleOne_eq_zero_iff] at hx
      obtain ⟨m, hm⟩ := hx
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, mem_traceSub]
      refine ⟨-m, ?_⟩
      rw [hm, AddMonoidHom.neg_apply, map_neg]
      simp [sub_eq_add_neg, add_comm],
    fun y => by
      obtain ⟨z, rfl⟩ := cohomologyπ_surjective A 1 y
      obtain ⟨α, hα, rfl⟩ := exists_eq_cocycleOne A hG hc z
      exact ⟨((⟨α, (mem_fixedSub_neg_act A).2 hα⟩ : fixedSub (-act A c)) : tateQuot (-act A c)),
        rfl⟩⟩

theorem h1Equiv_mk (α : fixedSub (-act A c)) :
    h1EquivOfOrderTwo A hG hc (α : tateQuot (-act A c)) =
      cohomologyπ A 1 (cocycleOne A hG hc α ((mem_fixedSub_neg_act A).1 α.2)) :=
  rfl

def h2Hom : fixedSub (act A c) →+ cohomology A 2 where
  toFun a := cohomologyπ A 2 (cocycleTwo A hG hc a ((mem_fixedSub_act A).1 a.2))
  map_zero' := by
    rw [← map_zero (cohomologyπ A 2).hom]
    congr 1
    apply cocycles_ext
    rw [cochainOf_cocycleTwo, map_zero, cochainOf_zero]
    funext v
    simp [cochainTwo]
  map_add' a b := by
    rw [← map_add]
    congr 1
    exact cocycleTwo_add A hG hc _ _ _ _ _

theorem h2Hom_apply (a : fixedSub (act A c)) :
    h2Hom A hG hc a = cohomologyπ A 2 (cocycleTwo A hG hc a ((mem_fixedSub_act A).1 a.2)) :=
  rfl

def h2EquivOfOrderTwo : tateQuot (act A c) ≃+ cohomology A 2 :=
  AddEquiv.ofBijective (QuotientAddGroup.lift _ (h2Hom A hG hc) (by
      intro a ha
      rw [AddSubgroup.mem_addSubgroupOf, mem_traceSub] at ha
      obtain ⟨y, hy⟩ := ha
      rw [AddMonoidHom.mem_ker, h2Hom_apply, cohomologyπ_cocycleTwo_eq_zero_iff]
      exact ⟨y, hy.symm⟩))
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
      rw [QuotientAddGroup.lift_mk, h2Hom_apply, cohomologyπ_cocycleTwo_eq_zero_iff] at hx
      obtain ⟨m, hm⟩ := hx
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, mem_traceSub]
      exact ⟨m, hm.symm⟩,
    fun y => by
      obtain ⟨z, rfl⟩ := cohomologyπ_surjective A 2 y
      obtain ⟨a, ha, e⟩ := exists_cohomologyπ_eq_cocycleTwo A hG hc z
      exact ⟨((⟨a, (mem_fixedSub_act A).2 ha⟩ : fixedSub (act A c)) : tateQuot (act A c)), e.symm⟩⟩

theorem h2Equiv_mk (a : fixedSub (act A c)) :
    h2EquivOfOrderTwo A hG hc (a : tateQuot (act A c)) =
      cohomologyπ A 2 (cocycleTwo A hG hc a ((mem_fixedSub_act A).1 a.2)) :=
  rfl

end Equivs

section Zero

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Fintype G] (A : Rep.{0} k G) [IsDiscreteRep A] {c : G}
  (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

omit [TopologicalSpace G] [IsTopologicalGroup G] [Fintype G] [IsDiscreteRep A] in
include hG in
theorem mem_invariants_of_fixed {a : A} (ha : A.ρ c a = a) : a ∈ A.ρ.invariants := by
  intro g
  rcases hG g with rfl | rfl
  · rw [map_one, Module.End.one_apply]
  · exact ha

def h0HomOfOrderTwo : fixedSub (act A c) →+ cohomologyTateZero A where
  toFun a := Submodule.Quotient.mk ((H0Iso A).inv.hom
    ⟨a, mem_invariants_of_fixed A hG ((mem_fixedSub_act A).1 a.2)⟩)
  map_zero' := by
    change Submodule.Quotient.mk ((H0Iso A).inv.hom 0) = 0
    rw [map_zero, Submodule.Quotient.mk_zero]
  map_add' a b := by
    rw [← Submodule.Quotient.mk_add, ← map_add]
    rfl

theorem h0Hom_apply (a : fixedSub (act A c)) :
    h0HomOfOrderTwo A hG a = Submodule.Quotient.mk ((H0Iso A).inv.hom
      ⟨a, mem_invariants_of_fixed A hG ((mem_fixedSub_act A).1 a.2)⟩) :=
  rfl

omit [Fintype G] in
theorem H0Iso_inv_injective : Function.Injective (H0Iso A).inv.hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

include hc in

def cohomZeroEquivContinuous : tateQuot (act A c) ≃+ cohomologyTateZero A :=
  AddEquiv.ofBijective (QuotientAddGroup.lift _ (h0HomOfOrderTwo A hG) (by
      intro a ha
      rw [AddSubgroup.mem_addSubgroupOf, mem_traceSub] at ha
      obtain ⟨y, hy⟩ := ha
      rw [AddMonoidHom.mem_ker, h0Hom_apply, Submodule.Quotient.mk_eq_zero, mem_normClasses_iff]
      have hN : A.ρ.norm y = a := by
        rw [norm_apply A hG hc]
        exact hy
      refine ⟨y, hN ▸ mem_invariants_of_fixed A hG ((mem_fixedSub_act A).1 a.2), ?_⟩
      congr 1
      exact Subtype.ext hN.symm))
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
      rw [QuotientAddGroup.lift_mk, h0Hom_apply, Submodule.Quotient.mk_eq_zero,
        mem_normClasses_iff] at hx
      obtain ⟨m, hm, e⟩ := hx
      have e' : (a : A) = A.ρ.norm m :=
        congrArg (fun x : A.ρ.invariants => (x : A)) (H0Iso_inv_injective A e)
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, mem_traceSub]
      refine ⟨m, ?_⟩
      exact (norm_apply A hG hc m).symm.trans e'.symm,
    fun y => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      set a := (H0Iso A).hom.hom x with ha
      have hfix : (a : A) ∈ fixedSub (act A c) := (mem_fixedSub_act A).2 (a.2 c)
      refine ⟨((⟨a, hfix⟩ : fixedSub (act A c)) : tateQuot (act A c)), ?_⟩
      rw [QuotientAddGroup.lift_mk, h0Hom_apply]
      congr 1
      change (H0Iso A).inv.hom a = x
      rw [ha, ← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply]⟩

theorem h0Equiv_mk (a : fixedSub (act A c)) :
    cohomZeroEquivContinuous A hG hc (a : tateQuot (act A c)) = Submodule.Quotient.mk ((H0Iso A).inv.hom
      ⟨a, mem_invariants_of_fixed A hG ((mem_fixedSub_act A).1 a.2)⟩) :=
  rfl

end Zero

end OrderTwo

end GroundTheory.ProfCoh
