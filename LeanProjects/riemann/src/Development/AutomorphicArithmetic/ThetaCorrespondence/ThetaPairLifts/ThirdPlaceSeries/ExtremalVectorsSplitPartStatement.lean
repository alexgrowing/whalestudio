import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEstimateStatementStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtremalVectorsSplitPart

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_estimate_statement' : _root_.GlobalTheory.BigOn.RationalityStatement' := by
  first | exact @_root_.GlobalTheory.BigOn.bigOn_ratSt | exact _root_.GlobalTheory.BigOn.bigOn_ratSt | (intros; apply _root_.GlobalTheory.BigOn.bigOn_ratSt <;> assumption)
end
