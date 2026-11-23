import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointMixedLower
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischer_pairing_adjoint_mixed_lower : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inr b) (Sum.inl a)) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inl a) G)) := by
  first | exact @GlobalTheory.CharPair.fockAct1_Eab_inr_inl_embS_pair | exact GlobalTheory.CharPair.fockAct1_Eab_inr_inl_embS_pair | (intros; apply GlobalTheory.CharPair.fockAct1_Eab_inr_inl_embS_pair <;> assumption)
