import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedRankinSelbergLocalFactor
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_rankin_selberg_local_factor : Ad3.Loc2 → Ad3.R.E4 := by
  first | exact @GlobalTheory.CompanionTheory.RSUnram.rankinSelberg_unramified | exact GlobalTheory.CompanionTheory.RSUnram.rankinSelberg_unramified | (intros; apply GlobalTheory.CompanionTheory.RSUnram.rankinSelberg_unramified <;> assumption)
