import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsteinSeriesAbsoluteConvergence
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epstein_series_absolute_convergence : Ad3.R.G3a := by
  first | exact @GlobalTheory.CompanionTheory.EpsteinTensorBound.g3a | exact GlobalTheory.CompanionTheory.EpsteinTensorBound.g3a | (intros; apply GlobalTheory.CompanionTheory.EpsteinTensorBound.g3a <;> assumption)
