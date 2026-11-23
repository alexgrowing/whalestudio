import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointMixedUpper
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischer_pairing_adjoint_mixed_upper : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inl a) (Sum.inr b)) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inr b) G)) := by
  first | exact @GlobalTheory.CharPair.pair_fockAct1_embS_up | exact GlobalTheory.CharPair.pair_fockAct1_embS_up | (intros; apply GlobalTheory.CharPair.pair_fockAct1_embS_up <;> assumption)
