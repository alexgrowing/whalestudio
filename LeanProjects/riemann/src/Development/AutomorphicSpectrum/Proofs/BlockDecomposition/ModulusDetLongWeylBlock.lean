import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.DeterminantLongWeyl

open scoped NNReal

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem det_long_weyl3 : ((GeneralLinearGroup.det (w3 : GL (Fin 3) F) : Fˣ) : F) = -1 := by
  simp only [GeneralLinearGroup.val_det_apply, w3]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem det_tinv {n : Type} [Fintype n] [DecidableEq n] (g : GL n F) :
    GeneralLinearGroup.det (tinv g) = (GeneralLinearGroup.det g)⁻¹ := by
  ext
  simp [tinv, GeneralLinearGroup.val_det_apply, Matrix.det_transpose]

theorem modulus_neg_one : modulus (-1 : F) = 1 := by
  have h : modulus (-1 : F) ^ 2 = 1 := by
    rw [sq, ← modulus_mul]
    simp [modulus_one]
  exact (pow_eq_one_iff_of_nonneg (by positivity) (by norm_num)).1 h

theorem mp_inv (a : Fˣ) (s : ℂ) : mp a⁻¹ s = mp a (-s) := by
  have h1 : mp a⁻¹ s * mp a s = 1 := by
    rw [← GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.mp_mul, inv_mul_cancel]
    simp [mp, modulus_one]
  have h2 : mp a (-s) * mp a s = 1 := by
    rw [← GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.mp_add, neg_add_cancel]
    simp [mp]
  have h3 : mp a s ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  exact mul_right_cancel₀ h3 (h1.trans h2.symm)

end D

theorem main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (h : GL (Fin 2) F),
    mp (GeneralLinearGroup.det (w3 * tinv (em h))) 1 = mp (GeneralLinearGroup.det h) (-1) := by
  intro F _ _ _ _ _ _ h
  have hw : mp (GeneralLinearGroup.det (w3 : GL (Fin 3) F)) 1 = 1 := by
    rw [GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.mp_one, det_long_weyl3, modulus_neg_one]
    simp
  rw [map_mul, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.mp_mul, hw, one_mul, det_tinv, mp_inv, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.mp_det_em]

end GlobalTheory.CompanionTheory.DeterminantLongWeyl
