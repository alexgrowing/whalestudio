import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchorBoundStatementStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AnchorHolds

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anchor_bound : _root_.GlobalTheory.CovTop.AnchorCondition := by
  first | exact @_root_.GlobalTheory.CovTop.anchor_holds_alt | exact _root_.GlobalTheory.CovTop.anchor_holds_alt | (intros; apply _root_.GlobalTheory.CovTop.anchor_holds_alt <;> assumption)
end
