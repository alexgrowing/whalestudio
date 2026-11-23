import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExpansionStatementStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumExpStAltAlt

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_expansion' : _root_.GlobalTheory.ExpTie.ExponentSumStatement := by
  first | exact @_root_.GlobalTheory.ExpTie.sumExpSt_alt | exact _root_.GlobalTheory.ExpTie.sumExpSt_alt | (intros; apply _root_.GlobalTheory.ExpTie.sumExpSt_alt <;> assumption)
end
