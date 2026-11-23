import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointUpperBlock
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischer_pairing_adjoint_upper_block : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a a' : Fin P) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inl a) (Sum.inl a')) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inl a') G)) := by
  first | exact @GlobalTheory.CharPair.ActSFirstBlock.pair_act_first_block | exact GlobalTheory.CharPair.ActSFirstBlock.pair_act_first_block | (intros; apply GlobalTheory.CharPair.ActSFirstBlock.pair_act_first_block <;> assumption)
