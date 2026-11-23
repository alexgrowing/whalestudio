import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergFifthOfSecond
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_fifth_of_second : Ad3.R.A2 → Ad3.R.A5 := by
  first | exact @GlobalTheory.CompanionTheory.RSPlane.measure_plane_eq_rows | exact GlobalTheory.CompanionTheory.RSPlane.measure_plane_eq_rows | (intros; apply GlobalTheory.CompanionTheory.RSPlane.measure_plane_eq_rows <;> assumption)
