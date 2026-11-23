import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftFourierCoefficients
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_fourier_coefficients : Ad3.R.B0 → Ad3.R.C1 → Ad3.R.U2 → Ad3.R.G0 → Ad3.R.G1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.F2 → Ad3.R.F3 → Ad3.R.F5 → Ad3.R.F4 := by
  first | exact @GlobalTheory.CompanionTheory.RSEigen.abs_eigenvalue_sq | exact GlobalTheory.CompanionTheory.RSEigen.abs_eigenvalue_sq | (intros; apply GlobalTheory.CompanionTheory.RSEigen.abs_eigenvalue_sq <;> assumption)
