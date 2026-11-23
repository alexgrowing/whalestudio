import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjOfTwistedNormEqGLOneUnramified
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_conj_of_twistedNorm_eq_GL_one_unramified : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ δ' : GL (Fin 1) (Qr p r), nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ = nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ' → ∃ h : GL (Fin 1) (Qr p r), δ' = h⁻¹ * δ * GlobalTheory.LKLoc.sig p (Q0 p) 1 r h := by
  first | (exact @GlobalTheory.LKMid.exists_sig_twisted_conj_of_nrmG_eq) | (exact GlobalTheory.LKMid.exists_sig_twisted_conj_of_nrmG_eq) | (intros; apply GlobalTheory.LKMid.exists_sig_twisted_conj_of_nrmG_eq  <;> assumption)
