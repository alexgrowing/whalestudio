import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory

theorem sl2_right_factor_of_coprime_factorizations :
    ∀ (a c : ℤ), IsCoprime a c → c ≠ 0 → ∀ (y y' β β' : Matrix (Fin 2) (Fin 2) ℤ),
      y.det = a → y'.det = a → β.det = c → β'.det = c → y * β = y' * β' →
      ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * β = β' := by
  intro a c hac hc y y' β β' hy hy' hβ hβ' hyβ
  set P : Matrix (Fin 2) (Fin 2) ℤ := β' * adjugate β with hP
  set Q : Matrix (Fin 2) (Fin 2) ℤ := adjugate y' * y with hQ
  have hPQ : a • P = c • Q := by
    have h1 : adjugate y' * y * β = a • β' := by
      rw [Matrix.mul_assoc, hyβ, ← Matrix.mul_assoc, adjugate_mul, hy', Matrix.smul_mul, Matrix.one_mul]
    have h2 : β * adjugate β = c • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [mul_adjugate, hβ]
    calc a • P = (a • β') * adjugate β := by rw [hP, Matrix.smul_mul]
      _ = adjugate y' * y * β * adjugate β := by rw [h1]
      _ = Q * (β * adjugate β) := by rw [hQ, Matrix.mul_assoc]
      _ = c • Q := by rw [h2, Matrix.mul_smul, Matrix.mul_one]
  have hdiv : ∀ i j, c ∣ P i j := by
    intro i j
    have := congrFun (congrFun hPQ i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact hac.symm.dvd_of_dvd_mul_left ⟨Q i j, this⟩
  choose M hM using hdiv
  set Mm : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of M with hMm
  have hPM : P = c • Mm := by
    ext i j; simp [hMm, hM i j]
  have hMβ : Mm * β = β' := by
    have : c • (Mm * β) = c • β' := by
      rw [← Matrix.smul_mul, ← hPM, hP, Matrix.mul_assoc, adjugate_mul, hβ, Matrix.mul_smul, Matrix.mul_one]
    ext i j
    have := congrFun (congrFun this i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hc this
  have hdet : Mm.det = 1 := by
    have h1 : P.det = c * c := by
      rw [hP, det_mul, det_adjugate, hβ, hβ']
      simp
    rw [hPM, det_smul] at h1
    simp at h1
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
    have : c ^ 2 * Mm.det = c ^ 2 * 1 := by rw [h1]; ring
    exact mul_left_cancel₀ hc2 this
  exact ⟨⟨Mm, hdet⟩, hMβ⟩

end GlobalTheory
