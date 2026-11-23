import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardQuotPrimeSmulEqCardKerMulPowFinrank
import Mathlib
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime], Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) = Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) * p ^ Module.finrank ℤ M := by
  first | exact @GlobalTheory.card_quot_prime_smul_eq_card_ker_mul_pow_finrank | exact GlobalTheory.card_quot_prime_smul_eq_card_ker_mul_pow_finrank | (intros; apply GlobalTheory.card_quot_prime_smul_eq_card_ker_mul_pow_finrank <;> assumption)
