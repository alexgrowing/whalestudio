import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanFittedIdentityStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ArchTie

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arch_tie_of_setAt_logDeriv : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.NormSum.ArchSt → BotSmall → _root_.GlobalTheory.BigTop.Fun.ArchimedeanCondition @Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.arch_tie_of_logDeriv_bound | exact _root_.GlobalTheory.BigTop.Fun.arch_tie_of_logDeriv_bound | (intros; apply _root_.GlobalTheory.BigTop.Fun.arch_tie_of_logDeriv_bound <;> assumption)
end
