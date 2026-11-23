import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximumEstimateStatementStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MaxSt

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximum_estimate_statement' : _root_.GlobalTheory.BigOn.MaximalityStatement := by
  first | exact @_root_.GlobalTheory.BigOn.maxSt_alt | exact _root_.GlobalTheory.BigOn.maxSt_alt | (intros; apply _root_.GlobalTheory.BigOn.maxSt_alt <;> assumption)
end
