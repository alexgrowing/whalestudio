import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderCyclic
import GroundTheory.TateCohomology.InfRes
import GroundTheory.LocalFields.RamificationStructure
import GroundTheory.LocalFields.IntermediateField
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits IntermediateField

universe u

section Transport

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

noncomputable def subgroupEquivGalFixedField (H : Subgroup Gal(L/K)) :
    H ≃* Gal(L/fixedField H) :=
  (MulEquiv.subgroupCongr (fixingSubgroup_fixedField H).symm).trans
    (fixingSubgroupEquiv (fixedField H))

noncomputable def groupCohomologyResGalUnitsIso (H : Subgroup Gal(L/K)) (n : ℕ) :
    groupCohomology (Rep.res H.subtype (galUnits.{u} K L)) n ≅
      groupCohomology (galUnits.{u} (fixedField H) L) n :=
  groupCohomology.mapIso (subgroupEquivGalFixedField H) (LinearEquiv.refl _ _)
    (fun _ => LinearMap.ext fun _ => rfl) n

theorem isZero_groupCohomology_one_res_galUnits (H : Subgroup Gal(L/K)) :
    IsZero (groupCohomology (Rep.res H.subtype (galUnits.{u} K L)) 1) :=
  (isZero_groupCohomology_one_galUnits (fixedField H) L).of_iso
    (groupCohomologyResGalUnitsIso H 1)

end Transport

section Step

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

def openNormalOfNormal (N : Subgroup Gal(L/K)) [N.Normal] : OpenNormalSubgroup Gal(L/K) where
  toSubgroup := N
  isOpen' := isOpen_discrete _
  isNormal' := inferInstance

theorem natCard_groupCohomology_two_galUnits_dvd_of_normal (N : Subgroup Gal(L/K)) [N.Normal]
    (hLE : Nat.card (groupCohomology (galUnits.{u} (fixedField N) L) 2) ∣
      Module.finrank (fixedField N) L)
    (hEK : Nat.card (groupCohomology (galUnits.{u} K (fixedField N)) 2) ∣
      Module.finrank K (fixedField N)) :
    Nat.card (groupCohomology (galUnits.{u} K L) 2) ∣ Module.finrank K L := by
  have h1 := isZero_groupCohomology_one_res_galUnits (K := K) (L := L) N
  have hinj := GroundTheory.GroupCoh.inflation_two_injective (A := galUnits.{u} K L) (S := N) h1
  have hex := GroundTheory.GroupCoh.range_inflation_two_eq_ker_restriction (A := galUnits.{u} K L) (S := N) h1
  set res := (GroundTheory.GroupCoh.restriction (galUnits.{u} K L) N 2).hom
  set infl := (GroundTheory.GroupCoh.inflation (galUnits.{u} K L) N 2).hom

  have hcard : Nat.card (groupCohomology (galUnits.{u} K L) 2) =
      Nat.card (LinearMap.range res) * Nat.card (LinearMap.ker res) := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker res),
      Nat.card_congr (LinearMap.quotKerEquivRange res).toEquiv, mul_comm]

  have hker : Nat.card (LinearMap.ker res) =
      Nat.card (groupCohomology (galUnits.{u} K (fixedField N)) 2) := by
    rw [← hex, ← Nat.card_congr (LinearEquiv.ofInjective infl hinj).toEquiv]
    exact Nat.card_congr (groupCohomologyQuotientGalUnitsIso (openNormalOfNormal N) 2).toLinearEquiv.toEquiv

  have hrange : Nat.card (LinearMap.range res) ∣
      Nat.card (groupCohomology (galUnits.{u} (fixedField N) L) 2) := by
    rw [← Nat.card_congr (groupCohomologyResGalUnitsIso N 2).toLinearEquiv.toEquiv]
    exact AddSubgroup.card_addSubgroup_dvd_card (LinearMap.range res).toAddSubgroup
  rw [hcard, hker, ← Module.finrank_mul_finrank K (fixedField N) L, mul_comm (Module.finrank K _)]
  exact Nat.mul_dvd_mul (hrange.trans hLE) hEK

end Step

section Solvable

theorem exists_normal_ne_bot_ne_top_of_not_isCyclic {G : Type*} [Group G] [Group.IsSolvable G]
    (h : ¬IsCyclic G) : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_contra hN
  push Not at hN
  have : Nontrivial G := by
    by_contra ht
    rw [not_nontrivial_iff_subsingleton] at ht
    exact h inferInstance
  have : IsSimpleGroup G :=
    { eq_bot_or_eq_top_of_normal := fun N hN' => by
        by_cases hb : N = ⊥
        · exact Or.inl hb
        · exact Or.inr (hN N hN' hb) }
  have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := G)).2 inferInstance
  let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := hcomm }
  exact h IsSimpleGroup.isCyclic

end Solvable

section Bound

theorem natCard_groupCohomology_two_galUnits_dvd_of_finrank (n : ℕ) :
    ∀ (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K]
      [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
      [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L],
      Module.finrank K L = n → Nat.card (groupCohomology (galUnits.{u} K L) 2) ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ hn
  subst hn
  by_cases hcyc : IsCyclic Gal(L/K)
  · exact (natCard_groupCohomology_two_galUnits_of_isCyclic (K := K) (L := L)).dvd
  have := GroundTheory.LocalField.isSolvable_algEquiv (K := K) (L := L)
  obtain ⟨N, hN, hbot, htop⟩ := exists_normal_ne_bot_ne_top_of_not_isCyclic hcyc
  have hpos : 0 < Module.finrank K (fixedField N) := Module.finrank_pos
  have hLE : Module.finrank (fixedField N) L = Nat.card N := finrank_fixedField_eq_card N
  have hmul := Module.finrank_mul_finrank K (fixedField N) L
  have hcardG : Nat.card Gal(L/K) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hNlt : Nat.card N < Module.finrank K L := by
    rw [← hcardG]
    exact lt_of_le_of_ne (Subgroup.card_le_card_group N)
      fun h => htop ((Subgroup.card_eq_iff_eq_top N).1 h)
  have hN1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).2 hbot
  apply natCard_groupCohomology_two_galUnits_dvd_of_normal N
  · exact ih _ (by rw [hLE]; exact hNlt) (fixedField N) L rfl
  · refine ih _ ?_ K (fixedField N) rfl
    rw [← hmul, hLE]
    exact lt_mul_right hpos hN1

end Bound

section Main

variable {K L : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

theorem natCard_groupCohomology_two_galUnits_dvd :
    Nat.card (groupCohomology (galUnits.{u} K L) 2) ∣ Module.finrank K L :=
  natCard_groupCohomology_two_galUnits_dvd_of_finrank _ K L rfl

theorem finite_groupCohomology_two_galUnits :
    Finite (groupCohomology (galUnits.{u} K L) 2) :=
  Nat.finite_of_card_ne_zero fun h =>
    Module.finrank_pos.ne' (Nat.eq_zero_of_zero_dvd (h ▸ natCard_groupCohomology_two_galUnits_dvd))

end Main

end GroundTheory.ProfCoh
