import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowMatrix
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_row_matrix : GlobalTheory.CompanionTheory.KerFc.RowMatrix := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.rowMatrix_holds | exact GlobalTheory.CompanionTheory.KerFc.rowMatrix_holds | (intros; apply GlobalTheory.CompanionTheory.KerFc.rowMatrix_holds <;> assumption)
