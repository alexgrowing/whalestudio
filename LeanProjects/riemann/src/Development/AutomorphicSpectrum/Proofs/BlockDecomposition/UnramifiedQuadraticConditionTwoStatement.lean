import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionTwo
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_two : PositivityTheory.SiegelWeilFormula.Gunr.Q2 := by
  first | exact @GlobalTheory.CompanionTheory.ValuationCompleteness.q2 | exact GlobalTheory.CompanionTheory.ValuationCompleteness.q2 | (intros; apply GlobalTheory.CompanionTheory.ValuationCompleteness.q2 <;> assumption)
