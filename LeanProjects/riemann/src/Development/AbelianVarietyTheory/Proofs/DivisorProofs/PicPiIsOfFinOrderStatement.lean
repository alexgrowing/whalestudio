import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicPiIsOfFinOrder
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pic_pi_isOfFinOrder' : ∀ (ι : Type) [Finite ι] (R : ι → Type) [∀ i, CommRing (R i)], (∀ i (M : CommRing.Pic (R i)), IsOfFinOrder M) → ∀ M : CommRing.Pic ((i : ι) → R i), IsOfFinOrder M := by
  first | exact @GlobalTheory.pic_pi_isOfFinOrder | exact GlobalTheory.pic_pi_isOfFinOrder | (intros; apply GlobalTheory.pic_pi_isOfFinOrder <;> assumption)
