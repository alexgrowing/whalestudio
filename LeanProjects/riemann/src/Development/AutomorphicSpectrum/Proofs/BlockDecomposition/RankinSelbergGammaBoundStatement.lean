import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGammaBound
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_gamma_bound : Ad3.R.RealPlaceGammaFactors := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.RealGamma.main | exact GlobalTheory.CompanionTheory.RankinSelberg.RealGamma.main | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.RealGamma.main <;> assumption)
