import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPointsSeparate
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_points_separate : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (C C' : Type) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C'] [Module.Flat R C'], Finite (C →ₐ[R] K) → (∀ a : C, (∀ ψ : C →ₐ[R] K, ψ a = 0) → a = 0) → (∀ a : C', (∀ ψ : C' →ₐ[R] K, ψ a = 0) → a = 0) → ∀ d : C ⊗[R] C', (∀ Ψ : C ⊗[R] C' →ₐ[R] K, Ψ d = 0) → d = 0 := by
  first | exact @GlobalTheory.tensor_eq_zero_of_points_separate | exact GlobalTheory.tensor_eq_zero_of_points_separate | (intros; apply GlobalTheory.tensor_eq_zero_of_points_separate <;> assumption)
