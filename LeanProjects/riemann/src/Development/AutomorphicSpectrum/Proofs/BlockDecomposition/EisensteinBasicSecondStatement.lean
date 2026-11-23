import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicSecond
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_basic_second : Ad3.R.B0 → Ad3.R.E2 := by
  first | exact @GlobalTheory.CompanionTheory.RankinEuler.e2 | exact GlobalTheory.CompanionTheory.RankinEuler.e2 | (intros; apply GlobalTheory.CompanionTheory.RankinEuler.e2 <;> assumption)
