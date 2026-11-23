import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingIntegralBottomRow
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_integral_bottom_row : Ad3.R.G2b → Ad3.R.G2c := by
  first | exact @GlobalTheory.CompanionTheory.RankinUnfold.complex_unfold_of_nonneg_unfold | exact GlobalTheory.CompanionTheory.RankinUnfold.complex_unfold_of_nonneg_unfold | (intros; apply GlobalTheory.CompanionTheory.RankinUnfold.complex_unfold_of_nonneg_unfold <;> assumption)
