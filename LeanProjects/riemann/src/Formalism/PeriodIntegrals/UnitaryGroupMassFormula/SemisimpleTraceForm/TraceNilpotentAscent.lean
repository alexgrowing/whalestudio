import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.TraceNilStep
import Lemmata.IdempotentTraceVanishing.TraceAevalEqZero

namespace PI.SSAscent.UnitaryGroupMassFormula

open Polynomial

theorem trace_nilpotent_ascent : TraceNilStep := by
  first | exact Bl.IdempotentTraceVanishing.goal1 .. | (apply Bl.IdempotentTraceVanishing.goal1 <;> assumption) | (intros; apply Bl.IdempotentTraceVanishing.goal1 <;> assumption) | (apply @Bl.IdempotentTraceVanishing.goal1 <;> assumption) | (intros; apply @Bl.IdempotentTraceVanishing.goal1 <;> assumption) | (apply @Bl.IdempotentTraceVanishing.goal1 <;> first | assumption | infer_instance)

end PI.SSAscent.UnitaryGroupMassFormula
