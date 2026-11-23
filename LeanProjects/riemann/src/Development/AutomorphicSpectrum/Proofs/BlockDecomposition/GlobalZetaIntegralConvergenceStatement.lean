import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalZetaIntegralConvergence
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_zeta_integral_convergence : Ad3.R.G1a → Ad3.R.G3 → Ad3.R.AdelicThetaPoissonSummation → Ad3.R.G4 := by
  first | exact @GlobalTheory.CompanionTheory.RSZeta.functional_equation | exact GlobalTheory.CompanionTheory.RSZeta.functional_equation | (intros; apply GlobalTheory.CompanionTheory.RSZeta.functional_equation <;> assumption)
