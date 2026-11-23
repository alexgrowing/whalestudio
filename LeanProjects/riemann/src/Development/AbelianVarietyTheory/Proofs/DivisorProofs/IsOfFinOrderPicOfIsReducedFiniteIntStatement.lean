import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOfFinOrderPicOfIsReducedFiniteInt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOfFinOrder_pic_of_isReduced_finite_int : ∀ (B : Type) [CommRing B] [IsReduced B] [Module.Finite ℤ B] (M : CommRing.Pic B), IsOfFinOrder M := by
  first | exact @GlobalTheory.PicReducedTors.pic_isOfFinOrder | exact GlobalTheory.PicReducedTors.pic_isOfFinOrder | (intros; apply GlobalTheory.PicReducedTors.pic_isOfFinOrder <;> assumption)
