import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulInvMulPosSemidefUniformBound
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniform_bound_smul_inv_add_sum_mul_mulVec : ∀ (g a : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (c C : ℝ), 0 < c → (∀ i, (B i).PosSemidef) → ∃ W : ℝ, ∀ (Y' : Matrix (Fin g) (Fin g) ℝ) (t : Fin a → ℝ), Y'.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y'.mulVec x) → (∀ x, x ⬝ᵥ Y'.mulVec x ≤ C * (x ⬝ᵥ x)) → (∀ i, 0 < t i) → ∀ i x, ‖(t i • ((Y' + ∑ l, t l • B l)⁻¹ * B i)).mulVec x‖ ≤ W * ‖x‖ := by
  first | exact @GlobalTheory.smul_inv_mul_posSemidef_uniform_bound | exact GlobalTheory.smul_inv_mul_posSemidef_uniform_bound | (intros; apply GlobalTheory.smul_inv_mul_posSemidef_uniform_bound <;> assumption)
