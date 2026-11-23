import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixConjTransposeBySymmetricTausskyZassenhaus
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_conj_transpose_by_symmetric_taussky_zassenhaus : ∀ (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι k), ∃ P : Matrix ι ι k, IsUnit P ∧ P.transpose = P ∧ P * A = A.transpose * P := by
  first | exact @GlobalTheory.SymmetricSimilarTranspose.main | exact GlobalTheory.SymmetricSimilarTranspose.main | (intros; apply GlobalTheory.SymmetricSimilarTranspose.main <;> assumption)
