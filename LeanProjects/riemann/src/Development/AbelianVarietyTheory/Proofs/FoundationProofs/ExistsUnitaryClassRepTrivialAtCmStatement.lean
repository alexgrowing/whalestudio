import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryClass_rep_trivial_at_cm : ∀ D : D7, oddRep D := by
  first | exact @GlobalTheory.NormSum.exists_rep_trivial_at | exact GlobalTheory.NormSum.exists_rep_trivial_at | (intros; apply GlobalTheory.NormSum.exists_rep_trivial_at <;> assumption)
