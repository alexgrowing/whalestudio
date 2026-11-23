import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_one : PositivityTheory.SiegelWeilFormula.Gunr.Q1 := by
  first | exact @GlobalTheory.CompanionTheory.ResidueInvolution.q1 | exact GlobalTheory.CompanionTheory.ResidueInvolution.q1 | (intros; apply GlobalTheory.CompanionTheory.ResidueInvolution.q1 <;> assumption)
