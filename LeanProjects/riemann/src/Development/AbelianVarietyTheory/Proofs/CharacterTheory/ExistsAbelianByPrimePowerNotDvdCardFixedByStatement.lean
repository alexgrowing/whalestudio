import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsAbelianByPrimePowerNotDvdCardFixedBy
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianByPrimePower_not_dvd_card_fixedBy : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ H : Subgroup G, AbByP H ∧ ¬ p ∣ Nat.card (MulAction.fixedBy (G ⧸ H) x) := by
  first | exact @GlobalTheory.BI.exists_abelianByPrimePower_not_dvd_card_fixedBy₂ | exact GlobalTheory.BI.exists_abelianByPrimePower_not_dvd_card_fixedBy₂ | (intros; apply GlobalTheory.BI.exists_abelianByPrimePower_not_dvd_card_fixedBy₂ <;> assumption)
