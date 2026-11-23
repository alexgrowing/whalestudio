import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsotropicDualOfSkewMatrix
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_dual_of_skew_matrix' : ∀ (r g : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε ψ : Fin g → Fin r → ℚ), Mqᵀ = -Mq → (∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0) → (∀ i j, ψ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) → ∃ φ : Fin g → Fin r → ℚ, (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) ∧ (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) ∧ ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by
  first | exact @GlobalTheory.exists_isotropic_dual_of_skew_matrix | exact GlobalTheory.exists_isotropic_dual_of_skew_matrix | (intros; apply GlobalTheory.exists_isotropic_dual_of_skew_matrix <;> assumption)
