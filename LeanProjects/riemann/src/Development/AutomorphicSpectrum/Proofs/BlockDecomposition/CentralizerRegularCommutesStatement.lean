import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralizerRegularCommutes
import Mathlib
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_regular_commutes : ∀ {n : ℕ} (U H A Y : Matrix (Fin n) (Fin n) ℂ), U ∈ Matrix.unitaryGroup (Fin n) ℂ → (Uᴴ * H * U).IsDiag → (Uᴴ * A * U).IsDiag → (∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j → (Uᴴ * A * U) i i = (Uᴴ * A * U) j j) → H * Y = Y * H → Y * A = A * Y := by
  first | exact @GlobalTheory.CompanionTheory.MatrixComm.commute_of_dominated_diag | exact GlobalTheory.CompanionTheory.MatrixComm.commute_of_dominated_diag | (intros; apply GlobalTheory.CompanionTheory.MatrixComm.commute_of_dominated_diag <;> assumption)
