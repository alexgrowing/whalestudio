import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeAbsFrobeniusApplyF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRedDual
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleDieudonneTranspose_absFrobenius_apply_F : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsEt) (l l' : Mod B G h), IsTr B (frobRing (p_eq_zero p k)) h h (absFrob (p_eq_zero p k) G) l l' → ∀ y, l' (B.F G.dual (dual_conn h) y) = p * WittVector.frobenius (l y) := by
  first | exact @GlobalTheory.Dieu.EtFromConn.isTr_absFrob_F | exact GlobalTheory.Dieu.EtFromConn.isTr_absFrob_F | (intros; apply GlobalTheory.Dieu.EtFromConn.isTr_absFrob_F <;> assumption)
