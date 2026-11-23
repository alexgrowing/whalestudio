import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTiltAutomorphismTransport
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tilt_automorphism_transport : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (γ : O ≃+* O), IsPsi ψ → IsPrimitiveRoot (root ε).untilt p → ∃ (Γ : RL p O Λ ≃+* RL p O Λ) (ε' : PreTilt O p), IsPrimitiveRoot (root ε').untilt p ∧ Γ (inA (xi ε)) = inA (xi ε') ∧ Γ (inA (mu ε)) = inA (mu ε') ∧ (∀ r, Γ (ψ r) = ψ (Γ r)) ∧ ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → ∃ f', IsTheta ((γ : O →+* O).comp σ) f' ∧ ∀ r, f' (Γ r) = γ (f r) := by
  first | exact @GlobalTheory.GammaAct.exists_tensor_action | exact GlobalTheory.GammaAct.exists_tensor_action | (intros; apply GlobalTheory.GammaAct.exists_tensor_action <;> assumption)
