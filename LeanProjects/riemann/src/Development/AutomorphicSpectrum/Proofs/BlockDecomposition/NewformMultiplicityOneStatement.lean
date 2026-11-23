import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformMultiplicityOne
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_multiplicity_one : Ad3.R.A2 → Ad3.R.C1 → Ad3.R.M1 := by
  first | exact @GlobalTheory.CompanionTheory.RankinTestVector.main | exact GlobalTheory.CompanionTheory.RankinTestVector.main | (intros; apply GlobalTheory.CompanionTheory.RankinTestVector.main <;> assumption)
