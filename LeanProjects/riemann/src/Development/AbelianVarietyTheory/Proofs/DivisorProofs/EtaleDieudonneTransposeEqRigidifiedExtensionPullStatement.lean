import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeEqRigidifiedExtensionPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRedDual
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleDieudonneTranspose_eq_rigidifiedExtensionPullback : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' : PDivGroup p k') (G : PDivGroup p k) (h' : G'.IsEt) (h : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G h) (l' : Mod B G' h'), IsTr B σ h' h s l l' → red B G' h' l' = s.rig (red B G h l) := by
  first | exact @GlobalTheory.Dieu.EtFromConn.red_of_isTr | exact GlobalTheory.Dieu.EtFromConn.red_of_isTr | (intros; apply GlobalTheory.Dieu.EtFromConn.red_of_isTr <;> assumption)
