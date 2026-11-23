import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedFunctionL2Positive
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_function_l2_positive : ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε) (f : UJ ε → D.V), f ∈ D.fns → ∀ g, f g ≠ 0 →
    0 < ∫ k : KG ε, ‖f k‖ ^ 2 ∂muK ε := by
  first | exact @GlobalTheory.RealInd.integral_norm_sq_pos_of_ne_zero | exact GlobalTheory.RealInd.integral_norm_sq_pos_of_ne_zero | (intros; apply GlobalTheory.RealInd.integral_norm_sq_pos_of_ne_zero <;> assumption)
