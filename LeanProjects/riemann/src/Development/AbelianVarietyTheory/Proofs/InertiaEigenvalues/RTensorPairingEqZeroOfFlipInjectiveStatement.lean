import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RTensorPairingEqZeroOfFlipInjective
import Mathlib
open TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_rTensor_pairing_eq_zero : ∀ (F : Type) [Field F] (B : Type) [AddCommGroup B] [Module F B] (V V' : Type) [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (m : V →ₗ[F] V' →ₗ[F] F), (∀ y, (∀ x, m x y = 0) → y = 0) → ∀ y : V' ⊗[F] B, (∀ v : V, TensorProduct.lid F B (LinearMap.rTensor B (m v) y) = 0) → y = 0 := by
  first | exact @GlobalTheory.rTensor_pairing_eq_zero_of_flip_injective | exact GlobalTheory.rTensor_pairing_eq_zero_of_flip_injective | (intros; apply GlobalTheory.rTensor_pairing_eq_zero_of_flip_injective <;> assumption)
