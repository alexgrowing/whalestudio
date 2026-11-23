import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointLowerBlock
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischer_pairing_adjoint_lower_block : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (b b' : Fin Q) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inr b) (Sum.inr b')) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inr b') G)) := by
  first | exact @GlobalTheory.CharPair.SecondBlockS.pair_fockAct1_inr_inr_embS | exact GlobalTheory.CharPair.SecondBlockS.pair_fockAct1_inr_inr_embS | (intros; apply GlobalTheory.CharPair.SecondBlockS.pair_fockAct1_inr_inr_embS <;> assumption)
