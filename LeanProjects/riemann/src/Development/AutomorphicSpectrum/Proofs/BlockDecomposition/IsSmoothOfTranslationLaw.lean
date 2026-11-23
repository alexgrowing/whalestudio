import Mathlib
import GroundTheory.AutomorphicForms.GL2.GodementSectionLocal
set_option maxSynthPendingDepth 1

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.GodementFix

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_congruence_fix {χ : Fˣ →* ℂˣ} (h : Continuous χ) {Φ : (Fin 2 → F) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 F) :
    ∃ m : ℕ, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m,
      rightTranslate u Φ = Φ ∧ χ (detU u) = 1 ∧ ∀ s : ℂ, modPow ((detU u : Fˣ) : F) s = 1 := by
  obtain ⟨N, M, hMN, hinv, hsupp⟩ := exists_invariant_of_mem_schwartzBruhat2 hΦ
  refine ⟨max (N - M).toNat (max (quasiCharConductor χ) 1), fun u hu ↦ ?_⟩
  set m := max (N - M).toNat (max (quasiCharConductor χ) 1) with hm
  have hu0 : u ∈ GLnLocal.integralGL F 2 := GLnLocal.congruenceSubgroup_le F 2 m hu
  refine ⟨?_, ?_, fun s ↦ ?_⟩
  · funext x
    simp only [rightTranslate]
    by_cases hx : x ∈ box F M
    · set D : Matrix (Fin 2) (Fin 2) F := (u : Matrix (Fin 2) (Fin 2) F) - 1 with hD
      have hxD : x ᵥ* D ∈ box F N := by
        refine box_antitone (show N ≤ M + m by omega) (mem_box.2 fun j ↦ ?_)
        simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
        exact add_mem (mul_mem_valBall (mem_box.1 hx 0)
            (sub_one_mem_valBall_of_mem_congruenceSubgroup hu 0 j))
          (mul_mem_valBall (mem_box.1 hx 1)
            (sub_one_mem_valBall_of_mem_congruenceSubgroup hu 1 j))
      have he : x ᵥ* (u : Matrix (Fin 2) (Fin 2) F) = x + x ᵥ* D := by
        rw [hD, Matrix.vecMul_sub, Matrix.vecMul_one]
        abel
      rw [he, hinv x _ hxD]
    · have h0 : Φ x = 0 := by
        by_contra h
        exact hx (hsupp x h)
      have h1 : Φ (x ᵥ* (u : Matrix (Fin 2) (Fin 2) F)) = 0 := by
        by_contra h
        exact hx ((vecMul_mem_box_iff hu0 M x).1 (hsupp _ h))
      rw [h0, h1]
  · have hmem : detU u ∈ unitFiltrationUnits F m :=
      (mem_unitFiltrationUnits_iff_valBall (by omega)).2 (det_sub_one_mem_valBall hu)
    exact unitFiltrationUnits_quasiCharConductor_le_ker h
      (unitFiltrationUnits_antitone (by omega) hmem)
  · rw [modPow_units_eq_zpow, ord_det_eq_zero hu0]
    simp

end GlobalTheory.CompanionTheory.GodementFix
