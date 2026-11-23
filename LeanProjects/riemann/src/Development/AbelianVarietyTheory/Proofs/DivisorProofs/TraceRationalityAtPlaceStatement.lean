import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRationalityAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_rationality_at_place : TraceOfAt := by
  first | exact @GlobalTheory.BigOn.Exp.SerBase.traceOfAt | exact GlobalTheory.BigOn.Exp.SerBase.traceOfAt | (intros; apply GlobalTheory.BigOn.Exp.SerBase.traceOfAt <;> assumption)
