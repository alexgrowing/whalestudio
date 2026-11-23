import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardQuotSpanEqFinsumLogNormEmbeddings
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_card_quot_span_eq_finsum_log_norm_embeddings : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] (b : B), b ≠ 0 → Finite (B ⧸ Ideal.span {b}) ∧ Real.log (Nat.card (B ⧸ Ideal.span {b})) = ∑ᶠ τ : B →+* ℂ, Real.log ‖τ b‖ := by
  first | exact @GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm | exact GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm | (intros; apply GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm <;> assumption)
