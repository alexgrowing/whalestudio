import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvOneAddPrimeMulPadic
import Mathlib
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_inv_one_add_prime_mul_padic : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S] (s : S), IsIntegral ℤ_[ℓ] s → ∃ r : S, (1 + (ℓ : S) * s) * r = 1 ∧ IsIntegral ℤ_[ℓ] r := by
  first | (exact @GlobalTheory.exists_integral_inv_one_add_prime_mul) | (exact GlobalTheory.exists_integral_inv_one_add_prime_mul) | (intros; apply GlobalTheory.exists_integral_inv_one_add_prime_mul  <;> assumption)
