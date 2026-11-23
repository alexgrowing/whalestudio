import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfied
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied : ∀ D, Inp D := by
  first | exact @GlobalTheory.NormSum.inp_all | exact GlobalTheory.NormSum.inp_all | (intros; apply GlobalTheory.NormSum.inp_all <;> assumption)
