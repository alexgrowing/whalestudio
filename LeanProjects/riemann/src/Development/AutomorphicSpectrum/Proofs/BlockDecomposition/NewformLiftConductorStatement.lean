import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftConductor
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_conductor : Ad3.R.B0 → Ad3.R.F0b := by
  first | exact @GlobalTheory.CompanionTheory.NewformLiftConductor.f0b | exact GlobalTheory.CompanionTheory.NewformLiftConductor.f0b | (intros; apply GlobalTheory.CompanionTheory.NewformLiftConductor.f0b <;> assumption)
