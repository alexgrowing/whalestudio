import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralAbsoluteConvergence
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_integral_absolute_convergence : Ad3.R.AdelicThetaPoissonSummation := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.theta_functional_equation | exact GlobalTheory.CompanionTheory.RankinSelberg.theta_functional_equation | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.theta_functional_equation <;> assumption)
