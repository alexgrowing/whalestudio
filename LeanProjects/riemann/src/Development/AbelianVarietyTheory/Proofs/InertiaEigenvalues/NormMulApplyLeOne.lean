import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint

open GlobalTheory.JR Matrix

noncomputable section

namespace GlobalTheory.JR.GLift

theorem norm_mul_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) (i j : Fin n) :
    ‖(A * B) i j‖ ≤ 1 := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)

theorem norm_one_apply_le_one {F : Type} [NormedField F] {n : ℕ} (i j : Fin n) :
    ‖(1 : Matrix (Fin n) (Fin n) F) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

def glOSub (n : ℕ) (F : Type) [NormedField F] [IsUltrametricDist F] : Subgroup (GL (Fin n) F) where
  carrier := glO n F
  mul_mem' {a b} ha hb := by
    intro i j
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact norm_mul_apply_le_one _ _ (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j
    · rw [_root_.mul_inv_rev, Units.val_mul]
      exact norm_mul_apply_le_one _ _ (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j
  one_mem' := by
    intro i j
    simp only [inv_one, Units.val_one]
    exact ⟨norm_one_apply_le_one i j, norm_one_apply_le_one i j⟩
  inv_mem' {a} ha := by
    intro i j
    rw [inv_inv]
    exact ⟨(ha i j).2, (ha i j).1⟩

theorem coe_glOSub (n : ℕ) (F : Type) [NormedField F] [IsUltrametricDist F] :
    (glOSub n F : Set (GL (Fin n) F)) = glO n F := rfl

end GlobalTheory.JR.GLift
