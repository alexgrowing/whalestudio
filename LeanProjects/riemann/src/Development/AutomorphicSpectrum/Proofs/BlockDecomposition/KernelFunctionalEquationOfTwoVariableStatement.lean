import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFunctionalEquationOfTwoVariable
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_functional_equation_of_two_variable : Ad3.R.A7 → Ad3.R.A8 := by
  first | exact @GlobalTheory.CompanionTheory.RSKernel.kernel_local_functional_equation | exact GlobalTheory.CompanionTheory.RSKernel.kernel_local_functional_equation | (intros; apply GlobalTheory.CompanionTheory.RSKernel.kernel_local_functional_equation <;> assumption)
