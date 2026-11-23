import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLogSpanTraceZero
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_log_span_trace_zero : ∀ (F : Type) [Field F] [NumberField F] (c : (F →+* ℂ) → ℝ), (∀ σ, c ((starRingEnd ℂ).comp σ) = c σ) → ∑ σ, c σ = 0 → ∃ (m : ℕ) (u : Fin m → (𝓞 F)ˣ) (r : Fin m → ℝ), ∀ σ, c σ = ∑ j, r j * Real.log (‖σ ((u j : 𝓞 F) : F)‖ ^ 2) := by
  first | exact @GlobalTheory.conjInvariant_sum_zero_eq_sum_log_units | exact GlobalTheory.conjInvariant_sum_zero_eq_sum_log_units | (intros; apply GlobalTheory.conjInvariant_sum_zero_eq_sum_log_units <;> assumption)
