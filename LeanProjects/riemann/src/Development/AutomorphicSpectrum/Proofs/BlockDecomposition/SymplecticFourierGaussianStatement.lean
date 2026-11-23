import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SymplecticFourierGaussian
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_fourier_gaussian : Ad3.R.B0 → Ad3.R.FT := by
  first | exact @GlobalTheory.CompanionTheory.RSFT.Assemble.fourier_gaussian_of_basic_facts | exact GlobalTheory.CompanionTheory.RSFT.Assemble.fourier_gaussian_of_basic_facts | (intros; apply GlobalTheory.CompanionTheory.RSFT.Assemble.fourier_gaussian_of_basic_facts <;> assumption)
