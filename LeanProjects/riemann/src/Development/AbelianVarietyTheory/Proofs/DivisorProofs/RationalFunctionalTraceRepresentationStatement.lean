import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionalTraceRepresentation
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_functional_trace_representation : ∀ (E : Type) [Field E] [NumberField E] (g : E →ₗ[ℚ] ℝ), (∀ z, ∃ q : ℚ, g z = q) →
    ∃ mu : E, ∀ z, g z = ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) := by
  first | exact @GlobalTheory.linearMap_rat_valued_eq_trace | exact GlobalTheory.linearMap_rat_valued_eq_trace | (intros; apply GlobalTheory.linearMap_rat_valued_eq_trace <;> assumption)
