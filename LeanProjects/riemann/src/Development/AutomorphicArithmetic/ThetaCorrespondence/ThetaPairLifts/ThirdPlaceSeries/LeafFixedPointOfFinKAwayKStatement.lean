import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAndAwayFormulaStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafFixedPointOfFinKAwayK

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leafFixedPoint_of_finK_awayK : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → FinK → AwayK → _root_.GlobalTheory.BigTop.Fun.LeafFixedPoint @Comparison₂ := by
  first | exact @_root_.GlobalTheory.Adopt.leafFixedPoint_of_finK_awayK | exact _root_.GlobalTheory.Adopt.leafFixedPoint_of_finK_awayK | (intros; apply _root_.GlobalTheory.Adopt.leafFixedPoint_of_finK_awayK <;> assumption)
end
