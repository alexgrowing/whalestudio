import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissibleSupersetFinitePlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitMemGlobalNormOfMemLocalNormsStatement

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem hasseNormSt : GlobalTheory.Published.HasseNormSt := by
  intro F _ _ δ x hδ hx hreal hfin
  classical
  by_cases hsq : IsSquare δ
  · exact GlobalTheory.Published.HasseNormSt.of_isSquare hδ hsq x
  obtain ⟨S, -, hS⟩ := exists_superset_mem_sUnits F {Units.mk0 δ hδ, Units.mk0 x hx} ∅
  obtain ⟨T, hST, hT⟩ := exists_admissible_superset_finite_places F S
  have hδT : Units.mk0 δ hδ ∈ sUnits F T := hS T hST _ (by simp)
  have hxT : Units.mk0 x hx ∈ sUnits F T := hS T hST _ (by simp)
  have hloc : Units.mk0 x hx ∈ locNorm F ((Units.mk0 δ hδ : Fˣ) : F) T := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · refine Subgroup.mem_iInf.mpr fun v => Subgroup.mem_iInf.mpr fun _ => ?_
      rw [mem_normSub]
      exact hfin v
    · refine Subgroup.mem_iInf.mpr fun σ => ?_
      rw [mem_normSub]
      exact hreal σ
  have h := GlobalTheory.T.sUnit_mem_globalNorm_of_mem_localNorms F (Units.mk0 δ hδ) T hT hδT hsq _ hxT hloc
  rw [mem_normSub] at h
  exact h

end GlobalTheory.QNorm
