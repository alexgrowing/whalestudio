import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicThird
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_basic_third : Ad3.R.B0 → Ad3.R.E3 := by
  first | exact @GlobalTheory.CompanionTheory.RSCompact.integral_prod_finAt | exact GlobalTheory.CompanionTheory.RSCompact.integral_prod_finAt | (intros; apply GlobalTheory.CompanionTheory.RSCompact.integral_prod_finAt <;> assumption)
