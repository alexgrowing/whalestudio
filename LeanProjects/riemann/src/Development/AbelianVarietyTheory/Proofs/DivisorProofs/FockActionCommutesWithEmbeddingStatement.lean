import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionCommutesWithEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_action_commutes_with_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inr b)) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inr b) G) := by
  first | exact @GlobalTheory.CharPair.fockAct1_Eab_inl_inr_embR | exact GlobalTheory.CharPair.fockAct1_Eab_inl_inr_embR | (intros; apply GlobalTheory.CharPair.fockAct1_Eab_inl_inr_embR <;> assumption)
