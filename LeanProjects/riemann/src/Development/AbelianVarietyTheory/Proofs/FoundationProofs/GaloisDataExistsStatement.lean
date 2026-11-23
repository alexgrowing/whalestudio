import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisDataExists
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_data_exists : ∀ D : D7, galEx D := by
  first | exact @GlobalTheory.GalExist.galEx_all | exact GlobalTheory.GalExist.galEx_all | (intros; apply GlobalTheory.GalExist.galEx_all <;> assumption)
