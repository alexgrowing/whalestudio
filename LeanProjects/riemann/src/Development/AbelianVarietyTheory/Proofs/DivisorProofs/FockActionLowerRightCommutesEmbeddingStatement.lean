import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionLowerRightCommutesEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_action_lower_right_commutes_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (b b' : Fin Q) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inr b) (Sum.inr b')) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inr b) (Sum.inr b') G) := by
  first | exact @GlobalTheory.CharPair.fockAct1_inr_inr_embR | exact GlobalTheory.CharPair.fockAct1_inr_inr_embR | (intros; apply GlobalTheory.CharPair.fockAct1_inr_inr_embR <;> assumption)
