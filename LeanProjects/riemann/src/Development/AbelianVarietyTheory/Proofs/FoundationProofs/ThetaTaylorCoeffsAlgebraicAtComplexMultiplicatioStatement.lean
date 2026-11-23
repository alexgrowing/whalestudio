import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication : ∀ D : D7, useAlg D := by
  first | exact @GlobalTheory.ThetaAlgebraic.taylor_algebraic | exact GlobalTheory.ThetaAlgebraic.taylor_algebraic | (intros; apply GlobalTheory.ThetaAlgebraic.taylor_algebraic <;> assumption)
