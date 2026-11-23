import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GLUpperTriangularEqDiagonalMulUnitriangular
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.GL_upperTriangular_eq_diagonal_mul_unitriangular' : ∀ (n : ℕ) (B : GL (Fin n) ℂ), B.val.BlockTriangular id → ∃ D U : GL (Fin n) ℂ, B = D * U ∧ D.val.IsDiag ∧ (∀ i, D.val i i = B.val i i) ∧ U.val.BlockTriangular id ∧ ∀ i, U.val i i = 1 := by
  first | exact @GlobalTheory.GL_upperTriangular_eq_diagonal_mul_unitriangular | exact GlobalTheory.GL_upperTriangular_eq_diagonal_mul_unitriangular | (intros; apply GlobalTheory.GL_upperTriangular_eq_diagonal_mul_unitriangular <;> assumption)
