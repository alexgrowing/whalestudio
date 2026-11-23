import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorRatAlgebraDecompFactorwise
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_rat_algebra_decomp_factorwise : ∀ (S F B : Type) [Field S] [CharZero S] [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B],
    ∃ (ι : Type) (_ : Fintype ι) (L : ι → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, CharZero (L i))
      (_ : ∀ i, Algebra F (L i)) (Φ : S ⊗[ℚ] B ≃+* ((i : ι) → L i ⊗[F] B)) (ψ : S ⊗[ℚ] F ≃+* ((i : ι) → L i)),
      (∀ b : B, Φ ((1 : S) ⊗ₜ[ℚ] b) = fun i => (1 : L i) ⊗ₜ[F] b) ∧
      (∀ z : S ⊗[ℚ] F, Φ (Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom ℚ F B) z) =
        fun i => algebraMap (L i) (L i ⊗[F] B) (ψ z i)) := by
  first | (exact @GlobalTheory.tensor_decomp_factorwise) | (exact GlobalTheory.tensor_decomp_factorwise) | (intros; apply GlobalTheory.tensor_decomp_factorwise  <;> assumption)
