import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfSurjectiveTensorSemilinear
import Mathlib
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_surjective_semilinear_tensor : ∀ (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k) (O : Type) [CommRing O] (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] O) M] [IsScalarTower Λ (Λ ⊗[ℤ] O) M], Module.Finite Λ M → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] O) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom] N), Function.Surjective f → Module.Finite (k ⊗[ℤ] O) N := by
  first | exact @GlobalTheory.finite_of_surjective_tensor_semilinear | exact GlobalTheory.finite_of_surjective_tensor_semilinear | (intros; apply GlobalTheory.finite_of_surjective_tensor_semilinear <;> assumption)
