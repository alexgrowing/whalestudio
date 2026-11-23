import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardEqFinsumLengthLocalizedMaximal
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_card_eq_finsum_length_localized_maximal : ∀ (B : Type) [CommRing B] (N : Type) [AddCommGroup N] [Module B N] [Finite N], Real.log (Nat.card N) = ∑ᶠ m : MaximalSpectrum B, ((Module.length (Localization.AtPrime m.asIdeal) (LocalizedModule m.asIdeal.primeCompl N)).toNat : ℝ) * Real.log (Nat.card (B ⧸ m.asIdeal)) := by
  first | exact @GlobalTheory.CardLength.log_card_eq_finsum_length | exact GlobalTheory.CardLength.log_card_eq_finsum_length | (intros; apply GlobalTheory.CardLength.log_card_eq_finsum_length <;> assumption)
