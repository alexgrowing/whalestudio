import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationLeCardOfSpan
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_pow_associated_le_card_of_span : ∀ (F : Type) [Field F] (T' T'' : Subring F), IsDiscreteValuationRing T' → IsDiscreteValuationRing T'' → ∀ (h : T' ≤ T''), (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) → ∀ (s : Finset F), (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) → ∀ π : T', Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ ∃ e : ℕ, 1 ≤ e ∧ e ≤ s.card ∧ Associated (Subring.inclusion h π) (ϖ ^ e) := by
  first | exact @GlobalTheory.ramification_le_card_of_span | exact GlobalTheory.ramification_le_card_of_span | (intros; apply GlobalTheory.ramification_le_card_of_span <;> assumption)
