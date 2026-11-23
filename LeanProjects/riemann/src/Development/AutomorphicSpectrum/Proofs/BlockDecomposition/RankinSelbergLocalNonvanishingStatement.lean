import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalNonvanishing
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_local_nonvanishing : Ad3.Loc2 → Ad3.R.A10 → Ad3.R.A11 := by
  first | exact @GlobalTheory.CompanionTheory.RSNonvanish.rankin_selberg_nonvanishing_of_whittaker | exact GlobalTheory.CompanionTheory.RSNonvanish.rankin_selberg_nonvanishing_of_whittaker | (intros; apply GlobalTheory.CompanionTheory.RSNonvanish.rankin_selberg_nonvanishing_of_whittaker <;> assumption)
