import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.InnerIntegralLongWeyl

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem em_inv_eq (h : GL (Fin 2) F) : (em h)⁻¹ = em h⁻¹ := by
  refine (eq_comm.1 (eq_inv_of_mul_eq_one_right ?_))
  apply Units.ext
  have hk : h.val * (h⁻¹ : GL (Fin 2) F).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Units.val_mul, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.em_val, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.em_val, Units.val_one]
  generalize (h⁻¹ : GL (Fin 2) F).val = K at hk ⊢
  generalize h.val = H at hk ⊢
  have e00 : H 0 0 * K 0 0 + H 0 1 * K 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hk 0) 0
  have e01 : H 0 0 * K 0 1 + H 0 1 * K 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hk 0) 1
  have e10 : H 1 0 * K 0 0 + H 1 1 * K 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hk 1) 0
  have e11 : H 1 0 * K 0 1 + H 1 1 * K 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hk 1) 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, e00, e01, e10, e11]

theorem block_long_weyl3_diag_concatenation (x : Fin 2 → F) (h : GL (Fin 2) F) :
    LFS.blk x * (w3 * tinv (em h) : GL (Fin 3) F).val = cat3 (col2 x * (tinv h).val) e1 := by
  have ht : (tinv (em h)).val = ((em h⁻¹).val)ᵀ := by
    change (((em h)⁻¹ : GL (Fin 3) F).val)ᵀ = _
    rw [em_inv_eq]
  have ht2 : (tinv h).val = ((h⁻¹ : GL (Fin 2) F).val)ᵀ := rfl
  rw [Units.val_mul, ht, ht2, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.em_val]
  generalize (h⁻¹ : GL (Fin 2) F).val = K
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LFS.blk, w3, cat3, col2, e1, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_three, Fin.sum_univ_two] <;> ring

theorem inner_integral_long_weyl_transpose_inv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), ∀ (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (y h : GL (Fin 2) F), LFS.inn ψ Φ y⁻¹ (w3 * tinv (em h)) = Lpart ψ (Pf Φ h y) := by
  intro F _ _ _ _ _ _ ψ Φ y h
  unfold LFS.inn Lpart Pf
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [Matrix.mul_assoc, block_long_weyl3_diag_concatenation, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.mul_concat_column, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.InnerIntegralLongWeyl
