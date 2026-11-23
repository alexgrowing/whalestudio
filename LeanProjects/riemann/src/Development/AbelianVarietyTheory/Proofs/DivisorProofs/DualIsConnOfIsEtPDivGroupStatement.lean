import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualIsConnOfIsEtPDivGroup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_isConn_of_isEt_pDivGroup : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt → G.dual.IsConn := by
  first | exact @GlobalTheory.PDivGroup.dual_isConn_of_isEt | exact GlobalTheory.PDivGroup.dual_isConn_of_isEt | (intros; apply GlobalTheory.PDivGroup.dual_isConn_of_isEt <;> assumption)
