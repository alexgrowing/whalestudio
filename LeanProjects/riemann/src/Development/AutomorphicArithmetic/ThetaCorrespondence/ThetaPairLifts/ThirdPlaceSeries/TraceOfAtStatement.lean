import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRationalityAtPlaceStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadComparisonAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceOfAtAltAlt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_rationality_at_place' : _root_.GlobalTheory.BigOn.Exp.SerBase.TraceAt' := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.SerBase.traceOfAt_alt | exact _root_.GlobalTheory.BigOn.Exp.SerBase.traceOfAt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.SerBase.traceOfAt_alt <;> assumption)
end
