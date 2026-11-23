import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGLVecMulEqLastBasis
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_vecMul_eq_last_basis : ∀ {k : Type} [Field k] (n : ℕ) (ξ : Fin (n + 1) → k), ξ ≠ 0 → ∃ g : GL (Fin (n + 1)) k, Matrix.vecMul ξ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = Pi.single (Fin.last n) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last | exact GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last | (intros; apply GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last <;> assumption)
