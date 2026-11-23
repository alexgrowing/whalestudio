import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackConstantSqEqDet
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPullbackConstant_sq_eq_det : ∀ D : D7, LemmaCGaussConstant D := by
  first | exact @GlobalTheory.UnitaryTheta.const_sq_eq_det | exact GlobalTheory.UnitaryTheta.const_sq_eq_det | (intros; apply GlobalTheory.UnitaryTheta.const_sq_eq_det <;> assumption)
