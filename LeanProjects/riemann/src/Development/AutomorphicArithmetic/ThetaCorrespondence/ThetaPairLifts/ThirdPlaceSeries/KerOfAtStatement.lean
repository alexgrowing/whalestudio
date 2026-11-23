import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRationalityAtPlaceStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadComparisonAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerOfAt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kerOfAt' : _root_.GlobalTheory.BigOn.Exp.SerBase.KerOfAtAlt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.SerBase.kerOfAt_alt | exact _root_.GlobalTheory.BigOn.Exp.SerBase.kerOfAt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.SerBase.kerOfAt_alt <;> assumption)
end
