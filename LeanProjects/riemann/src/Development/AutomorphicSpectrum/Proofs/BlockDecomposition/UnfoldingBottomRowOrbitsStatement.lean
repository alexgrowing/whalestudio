import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingBottomRowOrbits
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_bottom_row_orbits : Ad3.R.G2a := by
  first | exact @GlobalTheory.CompanionTheory.RSCoord.coord_exists | exact GlobalTheory.CompanionTheory.RSCoord.coord_exists | (intros; apply GlobalTheory.CompanionTheory.RSCoord.coord_exists <;> assumption)
