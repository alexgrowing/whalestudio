import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergThirdOfSecondFourth
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_third_of_second_fourth : Ad3.R.A2 → Ad3.R.A4 → Ad3.R.A3 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergTorusIntegrals.main | exact GlobalTheory.CompanionTheory.RankinSelbergTorusIntegrals.main | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergTorusIntegrals.main <;> assumption)
