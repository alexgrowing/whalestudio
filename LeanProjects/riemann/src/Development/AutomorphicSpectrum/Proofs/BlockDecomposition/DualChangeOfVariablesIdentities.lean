import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalEquationFourthHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair.ChangeVar

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem weyl_mul_weyl : (w2 : GL (Fin 2) F) * w2 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w2, Matrix.mul_apply, Fin.sum_univ_two]

theorem tinv_one' : tinv (1 : GL (Fin 2) F) = 1 := by
  apply Units.ext
  simp [tinv]

theorem transposeInv_weyl : tinv (w2 : GL (Fin 2) F) = w2 := by
  have hi : (w2 : GL (Fin 2) F)⁻¹ = w2 := inv_eq_of_mul_eq_one_left weyl_mul_weyl
  apply Units.ext
  change ((w2 : GL (Fin 2) F)⁻¹).valᵀ = (w2 : GL (Fin 2) F).val
  rw [hi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w2]

theorem tinv_tinv (z : GL (Fin 2) F) : tinv (tinv z) = z := by
  apply Units.ext
  change (z.valᵀ)ᵀ = z.val
  simp

theorem h_mul_inv (h z : GL (Fin 2) F) :
    h * (tinv z⁻¹ * w2 * h)⁻¹ = w2 * tinv z := by
  have h1 : tinv z⁻¹ * tinv z = 1 := by
    rw [← GlobalTheory.CompanionTheory.GL2LocalData.tinv_mul', inv_mul_cancel, tinv_one']
  have hi : (tinv z⁻¹)⁻¹ = tinv z := inv_eq_of_mul_eq_one_right h1
  have hw : (w2 : GL (Fin 2) F)⁻¹ = w2 := inv_eq_of_mul_eq_one_left weyl_mul_weyl
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hi, hw]
  group

theorem second_vector_long_weyl_transpose_inv (z : GL (Fin 2) F) :
    e2r (w2 * tinv z) = (z⁻¹ : GL (Fin 2) F).val *ᵥ e1 := by
  have hv : (w2 * tinv z).val = (w2 : GL (Fin 2) F).val * (z⁻¹ : GL (Fin 2) F).valᵀ := rfl
  unfold e2r
  rw [hv]
  generalize (z⁻¹ : GL (Fin 2) F).val = m
  ext j
  fin_cases j <;>
    simp [e1, w2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]

theorem dual_whittaker_long_weyl_transpose_inv (W₀ : GL (Fin 2) F → ℂ) (z : GL (Fin 2) F) :
    dW2 W₀ (w2 * tinv z) = W₀ z := by
  change W₀ (w2 * tinv (w2 * tinv z)) = W₀ z
  rw [GlobalTheory.CompanionTheory.GL2LocalData.tinv_mul', transposeInv_weyl, tinv_tinv, ← mul_assoc, weyl_mul_weyl, one_mul]

theorem modulus_neg_one : modulus (-1 : F) = 1 := by
  have h : modulus (-1 : F) * modulus (-1 : F) = 1 := by
    rw [← modulus_mul]
    simp
  have h2 : modulus (-1 : F) ^ 2 = 1 := by rw [sq]; exact h
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h2

theorem mp_of_val_neg (a : Fˣ) (s : ℂ) : mp (-a) s = mp a s := by
  have : modulus (-(a : F)) = modulus (a : F) := by
    rw [← neg_one_mul, modulus_mul, modulus_neg_one, one_mul]
  simp only [mp, Units.val_neg, this]

theorem det_g (h z : GL (Fin 2) F) :
    GeneralLinearGroup.det (tinv z⁻¹ * w2 * h) =
      -(GeneralLinearGroup.det z * GeneralLinearGroup.det h) := by
  apply Units.ext
  have h1 : (tinv z⁻¹).val = z.valᵀ := by
    change ((z⁻¹)⁻¹ : GL (Fin 2) F).valᵀ = z.valᵀ
    rw [inv_inv]
  have h2 : ((w2 : GL (Fin 2) F).val).det = -1 := by
    simp [w2, Matrix.det_fin_two]
  simp only [GeneralLinearGroup.val_det_apply, Units.val_mul, Units.val_neg, Matrix.det_mul, h1,
    Matrix.det_transpose, h2]
  ring

theorem main (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (W₀ : GL (Fin 2) F → ℂ) (h z : GL (Fin 2) F) (s : ℂ) :
    e2r (h * (tinv z⁻¹ * w2 * h)⁻¹) = (z⁻¹ : GL (Fin 2) F).val *ᵥ e1 ∧
    dW2 W₀ (h * (tinv z⁻¹ * w2 * h)⁻¹) = W₀ z ∧
    mp (GeneralLinearGroup.det (tinv z⁻¹ * w2 * h)) s =
      mp (GeneralLinearGroup.det z) s * mp (GeneralLinearGroup.det h) s := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h_mul_inv, second_vector_long_weyl_transpose_inv]
  · rw [h_mul_inv, dual_whittaker_long_weyl_transpose_inv]
  · rw [det_g, mp_of_val_neg, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.mp_mul]

end D

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair.ChangeVar
