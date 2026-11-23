import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAwayQuotientEqLocalization
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.away_quotient_span_eq_localization : ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D] [Algebra.Etale B D] (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → f ∈ P → ∀ (Q : Ideal D), Q.IsPrime → Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) → ∃ g : D, (∀ a : Localization.Away g, ∃ b : B, a - algebraMap B (Localization.Away g) b ∈ Ideal.span {algebraMap B (Localization.Away g) f}) ∧ ∀ b : B, algebraMap B (Localization.Away g) b ∈ Ideal.span {algebraMap B (Localization.Away g) f} ↔ ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.etale_away_quotient_eq_localization) | (exact GlobalTheory.etale_away_quotient_eq_localization) | (intros; apply GlobalTheory.etale_away_quotient_eq_localization  <;> assumption)
