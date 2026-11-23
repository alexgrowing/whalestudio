import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergUnfolding
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_unfolding : Ad3.R.G2a → Ad3.R.G2b → Ad3.R.G3a → Ad3.R.G3 := by
  first | exact @GlobalTheory.CompanionTheory.BottomRowCoordinates.g3 | exact GlobalTheory.CompanionTheory.BottomRowCoordinates.g3 | (intros; apply GlobalTheory.CompanionTheory.BottomRowCoordinates.g3 <;> assumption)
