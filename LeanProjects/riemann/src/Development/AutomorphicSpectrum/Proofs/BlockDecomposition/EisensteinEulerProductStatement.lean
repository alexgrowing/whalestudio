import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinEulerProduct
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_euler_product : Ad3.R.B0 → Ad3.R.M0 → Ad3.R.F3 → Ad3.R.E0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinWhittaker.whittaker_factorisation | exact GlobalTheory.CompanionTheory.RankinWhittaker.whittaker_factorisation | (intros; apply GlobalTheory.CompanionTheory.RankinWhittaker.whittaker_factorisation <;> assumption)
