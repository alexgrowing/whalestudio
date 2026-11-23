import Mathlib

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.RealPlace

theorem eq_diagonal_of_upperTriangular_of_unitary {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ)
    (hB : B.BlockTriangular id) (hBB : Bᴴ * B = 1) : B = diagonal (fun i => B i i) := by
  have hinv : B⁻¹ = Bᴴ := Matrix.inv_eq_left_inv hBB
  haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (Matrix.isUnit_det_of_left_inverse hBB)
  have hT : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB
  rw [hinv] at hT
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : Bᴴ j i = 0 := hT h
    rw [Matrix.conjTranspose_apply, star_eq_zero] at h1
    rw [h1, Matrix.diagonal_apply_ne _ (ne_of_lt h)]
  · simp
  · rw [hB h, Matrix.diagonal_apply_ne _ (ne_of_gt h)]

theorem flag_isometry_diagonal_on_frame (n r : ℕ) (J P p : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin r) ℂ) (hJ : IsUnit J.det) (hXY : Xᴴ * J * Y = 1)
    (_hP : P.PosDef) (_hPJ : P * J⁻¹ * P = J) (hPX : P * X = J * Y)
    (hpJ : pᴴ * J * p = J) (hpP : pᴴ * P * p = P)
    (B : Matrix (Fin r) (Fin r) ℂ) (hB : B.BlockTriangular id) (hpX : p * X = X * B) :
    ∃ d : Fin r → ℂ, p * X = X * diagonal d ∧ p * Y = Y * diagonal d := by
  have hXPX : Xᴴ * P * X = 1 := by
    rw [Matrix.mul_assoc, hPX, ← Matrix.mul_assoc]
    exact hXY
  have hBB : Bᴴ * B = 1 := by
    calc Bᴴ * B = Bᴴ * (Xᴴ * P * X) * B := by rw [hXPX, Matrix.mul_one]
      _ = (X * B)ᴴ * P * (X * B) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (p * X)ᴴ * P * (p * X) := by rw [hpX]
      _ = Xᴴ * (pᴴ * P * p) * X := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hpP]
          exact hXPX
  have hBd := eq_diagonal_of_upperTriangular_of_unitary B hB hBB
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin r) (Fin r) ℂ, D = diagonal (fun i => B i i) := ⟨_, rfl⟩
  have hBD : B = D := hBd.trans hD.symm
  have hpXD : p * X = X * D := by
    rw [hpX, hBD]
  have hr : pᴴ * (J * p * J⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hpJ, Matrix.mul_nonsing_inv J hJ]
  have hr' : (J * p * J⁻¹) * pᴴ = 1 := mul_eq_one_comm.mp hr
  have key : J * (p * Y) = J * (Y * D) := by
    calc J * (p * Y) = (J * p * J⁻¹) * pᴴ * (J * (p * Y)) := by rw [hr', Matrix.one_mul]
      _ = (J * p * J⁻¹) * (pᴴ * J * p) * Y := by simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * (J * Y) := by
          rw [hpJ]
          simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * (pᴴ * P * p * X) := by rw [hpP, hPX]
      _ = (J * p * J⁻¹) * pᴴ * (P * (p * X)) := by simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * pᴴ * (P * X * D) := by
          rw [hpXD]
          simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * pᴴ * (J * (Y * D)) := by
          rw [hPX]
          simp only [Matrix.mul_assoc]
      _ = J * (Y * D) := by rw [hr', Matrix.one_mul]
  have hpYD : p * Y = Y * D := by
    calc p * Y = J⁻¹ * (J * (p * Y)) := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul J hJ, Matrix.one_mul]
      _ = J⁻¹ * (J * (Y * D)) := by rw [key]
      _ = Y * D := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul J hJ, Matrix.one_mul]
  exact ⟨fun i => B i i, hD ▸ hpXD, hD ▸ hpYD⟩

end GlobalTheory.CompanionTheory.RealPlace
