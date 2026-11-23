import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeNakayamaApproximation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
open GlobalTheory.RingChain
open scoped TensorProduct Pointwise ChangeOfRings
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_nakayama_approximation : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (a : A) (g : R), algebraMap A R a = g → ModIso R a → ∀ (M M' : Type) [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module R M'] (e : R ⊗[A] M ≃ₗ[R] M'), (∀ z : M', ∃ y : M, z - e (1 ⊗ₜ y) ∈ g • (⊤ : Submodule R M')) ∧ ∀ y : M, e (1 ⊗ₜ y) ∈ g • (⊤ : Submodule R M') → y ∈ a • (⊤ : Submodule A M) := by
  first | exact @GlobalTheory.RingChain.modIso_tensor_mod | exact GlobalTheory.RingChain.modIso_tensor_mod | (intros; apply GlobalTheory.RingChain.modIso_tensor_mod <;> assumption)
