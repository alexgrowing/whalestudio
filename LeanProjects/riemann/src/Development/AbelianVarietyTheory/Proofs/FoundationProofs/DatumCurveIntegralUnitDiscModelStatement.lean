import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datum_curve_integral_unitDisc_model : ∀ D : D7, GL3Theta.modelEx D := by
  first | exact @GlobalTheory.UnitModel.modelEx_holds | exact GlobalTheory.UnitModel.modelEx_holds | (intros; apply GlobalTheory.UnitModel.modelEx_holds <;> assumption)
