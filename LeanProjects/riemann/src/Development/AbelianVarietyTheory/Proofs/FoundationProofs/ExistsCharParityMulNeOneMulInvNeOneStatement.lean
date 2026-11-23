import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharParityMulNeOneMulInvNeOne
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dirichletCharacter_parity_mul_ne_one_mul_inv_ne_one : ∀ (N r : ℕ) (χ : DirichletCharacter ℂ N) (sg : ℂ), 0 < N → r.Prime → 7 ≤ r → r ∣ N → (sg = 1 ∨ sg = -1) → ∃ θ : DirichletCharacter ℂ N, θ (-1) = sg ∧ θ * χ ≠ 1 ∧ θ * χ⁻¹ ≠ 1 := by
  first | exact @GlobalTheory.exists_char_parity_mul_ne_one_mul_inv_ne_one | exact GlobalTheory.exists_char_parity_mul_ne_one_mul_inv_ne_one | (intros; apply GlobalTheory.exists_char_parity_mul_ne_one_mul_inv_ne_one <;> assumption)
