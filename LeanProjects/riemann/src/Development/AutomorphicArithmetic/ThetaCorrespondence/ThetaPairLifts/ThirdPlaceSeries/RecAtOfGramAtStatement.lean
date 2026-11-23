import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RecursionOfGramBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecAtOfGramAt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_recursion_of_gram_bound : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftRecursive := by
  first | exact @_root_.GlobalTheory.CovTop.liftRecursive_of_gram | exact _root_.GlobalTheory.CovTop.liftRecursive_of_gram | (intros; apply _root_.GlobalTheory.CovTop.liftRecursive_of_gram <;> assumption)
end
