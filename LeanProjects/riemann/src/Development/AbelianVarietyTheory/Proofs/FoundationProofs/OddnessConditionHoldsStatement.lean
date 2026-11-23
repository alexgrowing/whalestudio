import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oddness_condition_holds : ∀ D : D7, odd4 D := by
  first | exact @GlobalTheory.VacuumScalar.vacuum_scalar | exact GlobalTheory.VacuumScalar.vacuum_scalar | (intros; apply GlobalTheory.VacuumScalar.vacuum_scalar <;> assumption)
