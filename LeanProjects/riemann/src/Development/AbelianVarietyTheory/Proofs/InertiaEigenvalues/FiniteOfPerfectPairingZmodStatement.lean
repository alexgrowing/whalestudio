import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteOfPerfectPairingZmod
open Function
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_bijective_pairing_zmod : ∀ (n : ℕ) [NeZero n] (A B C : Type) [AddCommGroup A] [Module (ZMod n) A] [AddCommGroup B] [Module (ZMod n) B] [AddCommGroup C] [Module (ZMod n) C] [Finite C] (b : A →ₗ[ZMod n] B →ₗ[ZMod n] C), Nonempty (C ≃ₗ[ZMod n] ZMod n) → Bijective b → Bijective b.flip → Finite A ∧ Finite B := by
  first | exact @GlobalTheory.finite_of_perfect_pairing_zmod | exact GlobalTheory.finite_of_perfect_pairing_zmod | (intros; apply GlobalTheory.finite_of_perfect_pairing_zmod <;> assumption)
