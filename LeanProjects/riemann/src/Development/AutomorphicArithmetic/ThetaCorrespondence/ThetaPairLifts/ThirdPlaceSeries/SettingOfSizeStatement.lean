import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetAtOfSizeAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingOfSize

set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.set_at_of_size_at' : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt | exact _root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt <;> assumption)
end
