import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringLeFromMeasureStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreLeOfGramMeasRat

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coreLe_of_gram_meas_liftRational : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.MeasureCondition → _root_.GlobalTheory.CovTop.LiftRational → _root_.GlobalTheory.CovTop.CoreBound' := by
  first | exact @_root_.GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat_alt | exact _root_.GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat_alt | (intros; apply _root_.GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat_alt <;> assumption)
end
