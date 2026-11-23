import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameTransitionPsiMatrix
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_transition_psi_matrix : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ψ : RL p O Λ →+* RL p O Λ) (e e' t t' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (X : Matrix (Fin h) (Fin h) (Ainf p O)) (Y : Matrix (Fin N) (Fin N) (RL p O Λ)), Function.Surjective ψ → (∀ w, t (fun i => ψ (w i)) = fun j => phiInv p O (e w j)) → (∀ w, t' (fun i => ψ (w i)) = fun j => phiInv p O (e' w j)) → IsMat e e' X Y → IsMat t t' (X.map (phiInv p O)) (Y.map ψ) := by
  first | exact @GlobalTheory.DetInv.isMat_twist | exact GlobalTheory.DetInv.isMat_twist | (intros; apply GlobalTheory.DetInv.isMat_twist <;> assumption)
