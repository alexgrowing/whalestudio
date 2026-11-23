import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSpanPowLeMulLength
import Mathlib
open Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_quotient_span_pow_le_mul_length : ∀ (O : Type) [CommRing O] (p : O) (n : ℕ), Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
  first | exact @GlobalTheory.main | exact GlobalTheory.main | (intros; apply GlobalTheory.main <;> assumption)
