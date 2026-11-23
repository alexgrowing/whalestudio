import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftWhittakerExpansion
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_whittaker_expansion : Ad3.R.F2 := by
  first | exact @GlobalTheory.CompanionTheory.RsWhittaker.whittaker_of_lift | exact GlobalTheory.CompanionTheory.RsWhittaker.whittaker_of_lift | (intros; apply GlobalTheory.CompanionTheory.RsWhittaker.whittaker_of_lift <;> assumption)
