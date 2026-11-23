import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_row_exists : GlobalTheory.CompanionTheory.KerFc.FactorRapid → GlobalTheory.CompanionTheory.KerFc.EvAdj → GlobalTheory.CompanionTheory.KerFc.RowExists := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.rowExists_of_factor | exact GlobalTheory.CompanionTheory.KerFc.rowExists_of_factor | (intros; apply GlobalTheory.CompanionTheory.KerFc.rowExists_of_factor <;> assumption)
