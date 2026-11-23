import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionLowerLeftCommutesEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_action_lower_left_commutes_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inr b) (Sum.inl a)) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inr b) (Sum.inl a) G) := by
  first | exact @GlobalTheory.CharPair.fockAct1_embR_inr_inl | exact GlobalTheory.CharPair.fockAct1_embR_inr_inl | (intros; apply GlobalTheory.CharPair.fockAct1_embR_inr_inl <;> assumption)
