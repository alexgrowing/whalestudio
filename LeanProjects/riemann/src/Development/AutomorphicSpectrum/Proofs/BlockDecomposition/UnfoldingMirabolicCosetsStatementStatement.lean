import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingMirabolicCosetsStatement
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_mirabolic_cosets_statement : Ad3.R.G2b := by
  first | exact @GlobalTheory.CompanionTheory.RSUnfold.unfolding_mirabolic_cosets | exact GlobalTheory.CompanionTheory.RSUnfold.unfolding_mirabolic_cosets | (intros; apply GlobalTheory.CompanionTheory.RSUnfold.unfolding_mirabolic_cosets <;> assumption)
