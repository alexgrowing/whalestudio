import Mathlib
import GroundTheory.AutomorphicForms.AdmissibleInduction
import GroundTheory.AutomorphicForms.CuspidalAdmissible
import GroundTheory.AutomorphicForms.JacquetAdmissible
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import GroundTheory.AutomorphicForms.IwahoriFactorization

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal Topology Filter Set

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem fixedVectors_jacquetRep_congruenceSubgroup (m : ℕ) :
    fixedVectors (jacquetRep F n β π) ((congruenceSubgroup F n m).subgroupOf (levi F n β)) =
      fixedVectors (jacquetAction F n β π) ((congruenceSubgroup F n m).subgroupOf (levi F n β)) := by
  ext x
  simp only [mem_fixedVectors]
  refine forall₂_congr fun y hy => ?_
  rw [jacquetRep, twist_apply, MonoidHom.comp_apply,
    invSqrtModular_leviIncl_of_mem y (congruenceSubgroup_le F n m (Subgroup.mem_subgroupOf.1 hy)),
    one_smul]

theorem isAdmissible_jacquetRep (hπ : IsAdmissible π) : IsAdmissible (jacquetRep F n β π) := by
  refine ⟨isSmooth_jacquetRep π hπ.1, fun L hLc hLo => ?_⟩
  obtain ⟨m₁, hm₁⟩ := exists_subgroupOf_congruenceSubgroup_subset (hLo.mem_nhds L.one_mem)
  set m := max m₁ 1
  have hle : (congruenceSubgroup F n m).subgroupOf (levi F n β) ≤ L := fun x hx =>
    hm₁ (Subgroup.mem_subgroupOf.2 (congruenceSubgroup_antitone F n (le_max_left _ _)
      (Subgroup.mem_subgroupOf.1 hx)))
  have : FiniteDimensional ℂ (fixedVectors π (congruenceSubgroup F n m)) :=
    hπ.2 _ (isCompact_congruenceSubgroup F n m) (isOpen_congruenceSubgroup F n m)
  have hfin : FiniteDimensional ℂ
      (fixedVectors (jacquetRep F n β π) ((congruenceSubgroup F n m).subgroupOf (levi F n β))) := by
    rw [fixedVectors_jacquetRep_congruenceSubgroup]
    exact Module.Finite.of_surjective _
      (jacquetFixedMap_surjective_congruenceSubgroup β hπ (le_max_right m₁ 1))
  exact Submodule.finiteDimensional_of_le (fixedVectors_antitone _ hle)

end Parabolic

end GroundTheory.Automorphic
