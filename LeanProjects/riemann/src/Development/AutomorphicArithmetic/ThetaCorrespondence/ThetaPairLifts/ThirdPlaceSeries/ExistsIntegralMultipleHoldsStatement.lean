import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingFunctionBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIntegralMultipleHolds

set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaling_function_bound' : _root_.GlobalTheory.BigTop.Fun.ScaleCondition := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.existsIntegralMultiple_holds_alt | exact _root_.GlobalTheory.BigTop.Fun.existsIntegralMultiple_holds_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.existsIntegralMultiple_holds_alt <;> assumption)
end
