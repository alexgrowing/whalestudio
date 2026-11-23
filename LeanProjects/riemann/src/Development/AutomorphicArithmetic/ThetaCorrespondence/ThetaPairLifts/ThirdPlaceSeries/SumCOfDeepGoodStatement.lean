import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumConstantOfDeepGoodStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumCOfDeepGood

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_c_of_deep_good : _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SumBoundCondition := by
  first | exact @_root_.GlobalTheory.CovTop.sumC_of_deepGood_alt | exact _root_.GlobalTheory.CovTop.sumC_of_deepGood_alt | (intros; apply _root_.GlobalTheory.CovTop.sumC_of_deepGood_alt <;> assumption)
end
