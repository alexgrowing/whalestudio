import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardFixedByQuotientEqRelIndexOfPRegular

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_fixedBy_quotient_eq_relIndex_normalizer_of_coprime : ∀ (G : Type) [Group G] [Finite G] (c : G) (p : ℕ) (H N : Subgroup G), Nat.Coprime (orderOf c) p → Subgroup.zpowers c ≤ H → (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) → (∀ g : G, g ∈ N ↔ ∀ d ∈ Subgroup.zpowers c, g * d * g⁻¹ ∈ Subgroup.zpowers c) → Nat.card (MulAction.fixedBy (G ⧸ H) c) = H.relIndex N := by
  first | exact @GlobalTheory.card_fixedBy_quotient_eq_relIndex_of_pRegular | exact GlobalTheory.card_fixedBy_quotient_eq_relIndex_of_pRegular | (intros; apply GlobalTheory.card_fixedBy_quotient_eq_relIndex_of_pRegular <;> assumption)
