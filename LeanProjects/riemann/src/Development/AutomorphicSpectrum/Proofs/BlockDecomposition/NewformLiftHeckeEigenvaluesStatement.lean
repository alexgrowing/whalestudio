import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftHeckeEigenvalues
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_hecke_eigenvalues : Ad3.R.B0 → Ad3.R.C0 → Ad3.R.C1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.AutomorphicLevelEquivariance → Ad3.R.HeckeSumLocalTranslates → Ad3.R.F3 := by
  first | exact @GlobalTheory.CompanionTheory.RankinHecke.hecke_types_of_lift | exact GlobalTheory.CompanionTheory.RankinHecke.hecke_types_of_lift | (intros; apply GlobalTheory.CompanionTheory.RankinHecke.hecke_types_of_lift <;> assumption)
