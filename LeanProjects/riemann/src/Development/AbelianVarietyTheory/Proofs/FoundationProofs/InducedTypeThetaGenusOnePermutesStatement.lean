import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedType_thetaGenusOne_permutes : ∀ D : D7, admG1 D ∧ EmbeddingPermutesTypes D := by
  first | exact @GlobalTheory.InducedType.induced_type | exact GlobalTheory.InducedType.induced_type | (intros; apply GlobalTheory.InducedType.induced_type <;> assumption)
