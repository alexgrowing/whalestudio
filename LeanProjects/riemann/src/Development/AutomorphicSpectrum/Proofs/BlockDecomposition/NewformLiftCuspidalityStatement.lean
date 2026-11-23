import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftCuspidality
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_cuspidality : Ad3.R.F6 := by
  first | exact @GlobalTheory.CompanionTheory.NewformLiftCuspidality.f6 | exact GlobalTheory.CompanionTheory.NewformLiftCuspidality.f6 | (intros; apply GlobalTheory.CompanionTheory.NewformLiftCuspidality.f6 <;> assumption)
