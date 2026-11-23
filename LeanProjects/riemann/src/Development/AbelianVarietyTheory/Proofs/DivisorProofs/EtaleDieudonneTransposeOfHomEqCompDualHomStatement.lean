import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeOfHomEqCompDualHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRedDual
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleDieudonneTranspose_ofHom_eq_comp_dualHom : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (hG : G.IsEt) (hH : H.IsEt) (f : G ⟶ H) (l : Mod B H hH), IsTr B (RingHom.id k) hG hH (SemiHom.ofHom f) l (l ∘ₗ B.map (dual_conn hH) (dual_conn hG) (dualHom G H f)) := by
  first | exact @GlobalTheory.Dieu.EtFromConn.isTr_ofHom | exact GlobalTheory.Dieu.EtFromConn.isTr_ofHom | (intros; apply GlobalTheory.Dieu.EtFromConn.isTr_ofHom <;> assumption)
