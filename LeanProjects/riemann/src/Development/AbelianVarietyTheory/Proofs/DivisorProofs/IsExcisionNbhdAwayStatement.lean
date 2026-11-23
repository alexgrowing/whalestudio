import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (h : A), IsExcisionNbhd A A' h → ∀ a b : A', a * b - 1 ∈ Ideal.span {algebraMap A A' h} → IsExcisionNbhd A (Localization.Away a) h := by
  first | (exact @GlobalTheory.EtC.isExcisionNbhd_away) | (exact GlobalTheory.EtC.isExcisionNbhd_away) | (intros; apply GlobalTheory.EtC.isExcisionNbhd_away  <;> assumption)
