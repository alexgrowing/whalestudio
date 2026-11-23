import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwinerUnitary_all : ∀ D : D7, IntertwinerUnitary D := by
  first | exact @GlobalTheory.theta_translation_intertwiner_unitary | exact GlobalTheory.theta_translation_intertwiner_unitary | (intros; apply GlobalTheory.theta_translation_intertwiner_unitary <;> assumption)
