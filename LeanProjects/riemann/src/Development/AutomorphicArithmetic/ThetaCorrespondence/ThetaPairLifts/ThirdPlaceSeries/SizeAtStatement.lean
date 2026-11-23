import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeAtHoldsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAtAltAlt

set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_at' : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt | exact _root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt <;> assumption)
end
