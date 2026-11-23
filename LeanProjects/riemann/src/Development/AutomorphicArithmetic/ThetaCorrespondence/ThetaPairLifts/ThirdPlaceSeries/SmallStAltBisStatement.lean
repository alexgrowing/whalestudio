import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialLatticesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStAltBis

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_tuple_statement_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.SmallnessCondition := by
  first | exact @_root_.GlobalTheory.SmallSpan.smallSt_alt | exact _root_.GlobalTheory.SmallSpan.smallSt_alt | (intros; apply _root_.GlobalTheory.SmallSpan.smallSt_alt <;> assumption)
end
