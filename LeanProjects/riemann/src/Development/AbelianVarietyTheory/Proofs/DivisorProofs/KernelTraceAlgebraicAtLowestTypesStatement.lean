import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTraceAlgebraicAtLowestTypes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelTrace_algebraic_at_lowestTypes : TraceRat := by
  first | exact @GlobalTheory.TraceRatPf.traceRat | exact GlobalTheory.TraceRatPf.traceRat | (intros; apply GlobalTheory.TraceRatPf.traceRat <;> assumption)
