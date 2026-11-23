import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvertibleMatrixLastLineGiven
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invertible_matrix_last_line_given : ∀ (k : Type) [Field k] (m : ℕ) (a : Fin (m + 1) → k), a ≠ 0 → ∃ g : GL (Fin (m + 1)) k, ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = a j := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_GL_lastRow_eq | exact GlobalTheory.CompanionTheory.MirFourier.exists_GL_lastRow_eq | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_GL_lastRow_eq <;> assumption)
