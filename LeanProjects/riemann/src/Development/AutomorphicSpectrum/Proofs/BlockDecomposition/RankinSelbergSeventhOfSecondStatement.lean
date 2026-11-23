import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergSeventhOfSecond
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_seventh_of_second : Ad3.R.A2 → Ad3.R.A7 := by
  first | exact @GlobalTheory.CompanionTheory.RSPlane.a7 | exact GlobalTheory.CompanionTheory.RSPlane.a7 | (intros; apply GlobalTheory.CompanionTheory.RSPlane.a7 <;> assumption)
