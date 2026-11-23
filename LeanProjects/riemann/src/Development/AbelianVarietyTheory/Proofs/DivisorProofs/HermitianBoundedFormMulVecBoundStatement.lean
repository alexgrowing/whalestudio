import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianBoundedFormMulVecBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
open Matrix GlobalTheory.MatDeriv
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_bounded_form_mulVec_bound : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : ℝ), M.IsHermitian → (∀ v : Fin n → ℂ, 0 ≤ (star v ⬝ᵥ M *ᵥ v).re ∧ (star v ⬝ᵥ M *ᵥ v).re ≤ c * ‖v‖ ^ 2) → ∀ x : Fin n → ℂ, ‖M *ᵥ x‖ ≤ 4 * n * c * ‖x‖ := by
  first | exact @GlobalTheory.hermitian_mulVec_norm_le_of_quadForm | exact GlobalTheory.hermitian_mulVec_norm_le_of_quadForm | (intros; apply GlobalTheory.hermitian_mulVec_norm_le_of_quadForm <;> assumption)
