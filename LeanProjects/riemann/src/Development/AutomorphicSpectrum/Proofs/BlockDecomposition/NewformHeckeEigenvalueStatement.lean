import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformHeckeEigenvalue
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_hecke_eigenvalue : Ad3.R.C1 → Ad3.R.U1 := by
  first | exact @GlobalTheory.CompanionTheory.WhitU.eq_zero_of_eigen | exact GlobalTheory.CompanionTheory.WhitU.eq_zero_of_eigen | (intros; apply GlobalTheory.CompanionTheory.WhitU.eq_zero_of_eigen <;> assumption)
