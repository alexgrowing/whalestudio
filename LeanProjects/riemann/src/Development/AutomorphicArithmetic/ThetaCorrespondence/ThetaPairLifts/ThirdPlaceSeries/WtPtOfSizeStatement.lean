import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPointOfSizeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtPtOfSize

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_pt_of_size : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.WtPtAlt := by
  first | exact @_root_.GlobalTheory.RefSum.DivWt.wt_pt_of_cov_size | exact _root_.GlobalTheory.RefSum.DivWt.wt_pt_of_cov_size | (intros; apply _root_.GlobalTheory.RefSum.DivWt.wt_pt_of_cov_size <;> assumption)
end
