import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_functional_equation : Ad3.R.A1 → Ad3.R.A6 → Ad3.R.A8 → Ad3.R.LocalGammaFunctionalEquation → Ad3.R.A9 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.a9_of_a0_a1_eigenbasis_a6 | exact GlobalTheory.CompanionTheory.RankinSelberg.a9_of_a0_a1_eigenbasis_a6 | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.a9_of_a0_a1_eigenbasis_a6 <;> assumption)
