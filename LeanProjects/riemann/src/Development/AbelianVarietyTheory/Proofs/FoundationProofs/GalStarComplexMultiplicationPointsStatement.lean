import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galStar_complexMultiplication_points : ∀ D : D7, galStar D := by
  first | exact @GlobalTheory.ConjPoint.galStar_holds | exact GlobalTheory.ConjPoint.galStar_holds | (intros; apply GlobalTheory.ConjPoint.galStar_holds <;> assumption)
