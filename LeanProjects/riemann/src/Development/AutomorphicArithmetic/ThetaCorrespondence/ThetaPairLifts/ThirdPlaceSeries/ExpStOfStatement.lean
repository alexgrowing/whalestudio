import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOfNumericsModelStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpStOf

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expSt_of_num_sumExp_model : Formalism.CohomologicalDescent.E.ExCut → _root_.GlobalTheory.ExpTie.NumStAlt → _root_.GlobalTheory.ExpTie.ExponentSumStatement → _root_.GlobalTheory.ExpTie.ModelStatement → _root_.GlobalTheory.BigOn.ExponentStatement := by
  first | exact @_root_.GlobalTheory.ExpTie.Asm.expSt_of_alt | exact _root_.GlobalTheory.ExpTie.Asm.expSt_of_alt | (intros; apply _root_.GlobalTheory.ExpTie.Asm.expSt_of_alt <;> assumption)
end
