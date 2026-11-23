import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumNorm_conj_cmPoints_all_embeddings : ∀ D : D7, useNorm D := by
  first | exact @GlobalTheory.ConjNorm.useNorm_all | exact GlobalTheory.ConjNorm.useNorm_all | (intros; apply GlobalTheory.ConjNorm.useNorm_all <;> assumption)
