import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergArchimedeanFactor
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_archimedean_factor : Ad3.R.HalfPlaneAnalyticIdentities := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.x1a | exact GlobalTheory.CompanionTheory.RankinSelberg.x1a | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.x1a <;> assumption)
