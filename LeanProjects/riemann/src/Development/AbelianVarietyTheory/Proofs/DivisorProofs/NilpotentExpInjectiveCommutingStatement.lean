import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentExpInjectiveCommuting
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotent_exp_injective_commuting : ∀ (A : Type) [Ring A] [Algebra ℚ A] (a b : A), Commute a b → IsNilpotent a → IsNilpotent b → IsNilpotent.exp a = IsNilpotent.exp b → a = b := by
  first | exact @GlobalTheory.exp_injective_of_commute | exact GlobalTheory.exp_injective_of_commute | (intros; apply GlobalTheory.exp_injective_of_commute <;> assumption)
