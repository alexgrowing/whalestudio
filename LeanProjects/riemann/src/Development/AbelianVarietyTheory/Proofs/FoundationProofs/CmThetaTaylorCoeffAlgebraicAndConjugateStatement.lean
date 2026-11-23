import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forall_use1 : ∀ D : D7, use1 D := by
  first | exact @GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate | exact GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate | (intros; apply GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate <;> assumption)
