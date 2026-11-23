import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepTraceEqMulTrace
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_ringHom_eq_mul_algebraTrace : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (s : ℕ), r = s * Module.finrank ℚ E → ∀ a : 𝓞 E, (ρ a).trace = s * Algebra.trace ℤ (𝓞 E) a := by
  first | exact @GlobalTheory.repTrace_eq_mul_trace | exact GlobalTheory.repTrace_eq_mul_trace | (intros; apply GlobalTheory.repTrace_eq_mul_trace <;> assumption)
