import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelActionFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_action_formula : GlobalTheory.CompanionTheory.KerFc.LtSob → GlobalTheory.CompanionTheory.KerFc.LtComm → GlobalTheory.CompanionTheory.KerFc.ActFormula := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.actFormula | exact GlobalTheory.CompanionTheory.KerFc.actFormula | (intros; apply GlobalTheory.CompanionTheory.KerFc.actFormula <;> assumption)
