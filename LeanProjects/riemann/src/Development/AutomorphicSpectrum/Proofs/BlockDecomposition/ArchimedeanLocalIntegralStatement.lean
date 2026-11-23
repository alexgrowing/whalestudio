import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalIntegral
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_local_integral : Ad3.R.E5 := by
  first | exact @GlobalTheory.CompanionTheory.RealArchimedeanCharacter.E5 | exact GlobalTheory.CompanionTheory.RealArchimedeanCharacter.E5 | (intros; apply GlobalTheory.CompanionTheory.RealArchimedeanCharacter.E5 <;> assumption)
