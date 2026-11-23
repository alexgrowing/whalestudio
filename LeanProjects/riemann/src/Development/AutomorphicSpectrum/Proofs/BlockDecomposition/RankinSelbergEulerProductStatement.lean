import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergEulerProduct
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_euler_product : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.A10 → Ad3.R.E2 → Ad3.R.E3 → Ad3.R.E5 → Ad3.R.UnramifiedEulerProductIntegral → Ad3.R.F2 → Ad3.R.E6 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.Unfolded.e6 | exact GlobalTheory.CompanionTheory.RankinSelberg.Unfolded.e6 | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.Unfolded.e6 <;> assumption)
