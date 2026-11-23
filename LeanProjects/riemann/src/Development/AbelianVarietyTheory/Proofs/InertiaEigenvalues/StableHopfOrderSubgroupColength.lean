import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjLowUni
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

open Matrix

theorem schurSquareMatrixToBlocks_mul {R : Type} [CommRing R] {m r : ℕ} (M N : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    blk (M * N) = blk M * blk N := by
  simp only [blk]
  exact (Matrix.submatrix_mul_equiv M N _ _ _).symm

theorem schur_mul_conjLowUni : ∀ (R : Type) [CommRing R] (m r : ℕ) (g k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R), IsUnit (Dof g).det → IsUnit (Dof (conjLowUni (Yof g) k)).det → IsUnit (Dof (g * k)).det ∧ Dof (g * k) = Dof g * Dof (conjLowUni (Yof g) k) ∧ Yof (g * k) = Yof g + Yof (conjLowUni (Yof g) k) ∧ Scof (g * k) = Scof g * Scof (conjLowUni (Yof g) k) ∧ Xof (g * k) = Xof g + Scof g * Xof (conjLowUni (Yof g) k) * (Dof g)⁻¹ := by
  intro R _ m r g k hD hD'
  have hL : ∀ Z : Matrix (Fin (r + 1)) (Fin (m + 1)) R, blk (lowUni Z) = fromBlocks 1 0 Z 1 :=
    fun Z => blk_unblk _
  have hLL : ∀ Z : Matrix (Fin (r + 1)) (Fin (m + 1)) R,
      fromBlocks (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R) 0 (-Z) (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) R) * fromBlocks 1 0 Z 1 = 1 := by
    intro Z
    rw [fromBlocks_multiply]
    simp [fromBlocks_one]
  set Y := Yof g with hY
  set k' := conjLowUni Y k with hk'
  have hK : blk k' = fromBlocks 1 0 Y 1 * blk k * fromBlocks 1 0 (-Y) 1 := by
    rw [hk', conjLowUni, schurSquareMatrixToBlocks_mul, schurSquareMatrixToBlocks_mul, hL, hL]
  have hkk : blk k = fromBlocks 1 0 (-Y) 1 * blk k' * fromBlocks 1 0 Y 1 := by
    rw [hK]
    calc blk k = 1 * blk k * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
      _ = (fromBlocks 1 0 (-Y) 1 * fromBlocks 1 0 Y 1) * blk k * (fromBlocks 1 0 (-Y) 1 * fromBlocks 1 0 Y 1) := by
          rw [hLL]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hG : blk g = fromBlocks (Aof g) (Bof g) (Cof g) (Dof g) := (fromBlocks_toBlocks _).symm
  have hK' : blk k' = fromBlocks (Aof k') (Bof k') (Cof k') (Dof k') := (fromBlocks_toBlocks _).symm
  set A := Aof g
  set B := Bof g
  set C := Cof g
  set D := Dof g
  set A' := Aof k'
  set B' := Bof k'
  set C' := Cof k'
  set D' := Dof k'
  set Sc := Scof g with hSc
  have i1 : D⁻¹ * D = 1 := nonsing_inv_mul D hD
  have i2 : D * D⁻¹ = 1 := mul_nonsing_inv D hD
  have i3 : D'⁻¹ * D' = 1 := nonsing_inv_mul D' hD'
  have i4 : D' * D'⁻¹ = 1 := mul_nonsing_inv D' hD'
  have j1 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D⁻¹ * (D * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i1, Matrix.one_mul]
  have j2 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D * (D⁻¹ * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i2, Matrix.one_mul]
  have j3 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D'⁻¹ * (D' * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i3, Matrix.one_mul]
  have j4 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D' * (D'⁻¹ * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i4, Matrix.one_mul]
  have hGL : blk g * fromBlocks 1 0 (-Y) 1 = fromBlocks Sc B 0 D := by
    rw [hG, fromBlocks_multiply]
    congr 1
    · rw [hSc, Scof, hY, Yof]; simp only [Matrix.mul_one, Matrix.mul_neg, Matrix.mul_assoc]; abel
    · simp
    · have hDY : D * Y = C := j2 C
      rw [Matrix.mul_one, Matrix.mul_neg, hDY, add_neg_cancel]
    · simp
  have hprod : blk (g * k) = fromBlocks (Sc * A' + B * C' + (Sc * B' + B * D') * Y) (Sc * B' + B * D')
      (D * C' + D * D' * Y) (D * D') := by
    rw [schurSquareMatrixToBlocks_mul, hkk, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGL, hK', fromBlocks_multiply, fromBlocks_multiply]
    simp
  have eD : Dof (g * k) = D * D' := by simp only [Dof, hprod, toBlocks_fromBlocks₂₂]
  have eC : Cof (g * k) = D * C' + D * D' * Y := by simp only [Cof, hprod, toBlocks_fromBlocks₂₁]
  have eB : Bof (g * k) = Sc * B' + B * D' := by simp only [Bof, hprod, toBlocks_fromBlocks₁₂]
  have eA : Aof (g * k) = Sc * A' + B * C' + (Sc * B' + B * D') * Y := by simp only [Aof, hprod, toBlocks_fromBlocks₁₁]
  refine ⟨?_, eD, ?_, ?_, ?_⟩
  · rw [eD, det_mul]; exact hD.mul hD'
  · rw [Yof, Yof, eD, eC, Matrix.mul_inv_rev]
    simp only [Matrix.mul_add, Matrix.mul_assoc, j1, j3]
    abel
  · rw [Scof, Scof, eA, eB, eC, eD, Matrix.mul_inv_rev]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, j1, j3, j4]
    abel
  · rw [Xof, Xof, Xof, eB, eD, Matrix.mul_inv_rev]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, j4, i4]
    abel

end GlobalTheory.SchurExt
