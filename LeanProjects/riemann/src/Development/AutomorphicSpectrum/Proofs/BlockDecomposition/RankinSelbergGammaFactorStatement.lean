import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGammaFactor
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_gamma_factor : Ad3.R.LocalGammaFunctionalEquation := by
  first | exact @GlobalTheory.CompanionTheory.TateGamma.gam_strip | exact GlobalTheory.CompanionTheory.TateGamma.gam_strip | (intros; apply GlobalTheory.CompanionTheory.TateGamma.gam_strip <;> assumption)
