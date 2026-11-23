import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsSeventhEstimateStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RamifiedSumsSeventhBound

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramified_sum_bound' : _root_.GlobalTheory.BigTop.Fun.RamifiedSumBound' := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.ramified_sums_seventh_bound_alt | exact _root_.GlobalTheory.BigTop.Fun.ramified_sums_seventh_bound_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.ramified_sums_seventh_bound_alt <;> assumption)
end
