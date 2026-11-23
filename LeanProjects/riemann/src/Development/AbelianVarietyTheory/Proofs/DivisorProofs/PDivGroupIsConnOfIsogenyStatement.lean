import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsConnOfIsogeny
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_isConn_of_isogeny : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → G.IsConn → H.IsConn := by
  first | exact @GlobalTheory.Dieu.isConn_of_isIsog | exact GlobalTheory.Dieu.isConn_of_isIsog | (intros; apply GlobalTheory.Dieu.isConn_of_isIsog <;> assumption)
