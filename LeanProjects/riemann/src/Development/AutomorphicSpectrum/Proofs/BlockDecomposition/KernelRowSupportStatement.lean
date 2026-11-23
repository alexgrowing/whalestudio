import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_row_support : GlobalTheory.CompanionTheory.KerFc.SupportRow := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.supportRow | exact GlobalTheory.CompanionTheory.KerFc.supportRow | (intros; apply GlobalTheory.CompanionTheory.KerFc.supportRow <;> assumption)
