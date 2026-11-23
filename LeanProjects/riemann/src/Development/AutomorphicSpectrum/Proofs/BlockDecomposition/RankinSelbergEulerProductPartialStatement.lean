import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergEulerProductPartial
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_euler_product_partial : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.A10 → Ad3.R.M0 → Ad3.R.E4 → Ad3.R.E0 → Ad3.R.E1 → Ad3.R.E2 → Ad3.R.UnramifiedEulerProductIntegral := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergEulerProduct.e6a | exact GlobalTheory.CompanionTheory.RankinSelbergEulerProduct.e6a | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergEulerProduct.e6a <;> assumption)
