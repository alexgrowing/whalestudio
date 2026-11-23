import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixNormBlockReduction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open GlobalTheory.TriFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_norm_block_reduction : ∀ {C : Type} [NormedField C] {r : ℕ} (N : Matrix (Fin (r+1)) (Fin (r+1)) C), N 0 0 ≠ 0 → (∀ l : Fin r, N l.succ 0 = 0) → ∀ i : Fin r, matNorm N i.succ = matNorm (N.submatrix Fin.succ Fin.succ) i := by
  first | exact @GlobalTheory.TriFrame.matNorm_succ_of_blockTri | exact GlobalTheory.TriFrame.matNorm_succ_of_blockTri | (intros; apply GlobalTheory.TriFrame.matNorm_succ_of_blockTri <;> assumption)
