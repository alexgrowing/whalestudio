import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayCongrModOfIsCoprime
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.away_congr_mod_of_isCoprime : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → (∀ c : C, ∃ a : A, c - algebraMap A C a ∈ Ideal.span {algebraMap A C g}) → ∀ c' : Localization.Away (algebraMap A C f), ∃ b : Localization.Away f, c' - Localization.awayMap (algebraMap A C) f b ∈ Ideal.span {Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) g)} := by
  first | (exact @GlobalTheory.away_congr_of_isCoprime) | (exact GlobalTheory.away_congr_of_isCoprime) | (intros; apply GlobalTheory.away_congr_of_isCoprime <;> assumption)
