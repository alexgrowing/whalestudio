import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCentralizerInjectiveCommutantEq
import Mathlib
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_centralizer_injective_commutant_eq : ∀ (K : Type) [Field K] [Algebra ℚ K] (C : Type) [Ring C] [Algebra ℚ C] (y : C),
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val) ∧
    ∀ w : K ⊗[ℚ] C, Commute w ((1 : K) ⊗ₜ[ℚ] y) → ∃ w' : K ⊗[ℚ] (Subalgebra.centralizer ℚ ({y} : Set C)),
      Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val w' = w := by
  first | (exact @GlobalTheory.tensor_centralizer_flat) | (exact GlobalTheory.tensor_centralizer_flat) | (intros; apply GlobalTheory.tensor_centralizer_flat <;> assumption)
