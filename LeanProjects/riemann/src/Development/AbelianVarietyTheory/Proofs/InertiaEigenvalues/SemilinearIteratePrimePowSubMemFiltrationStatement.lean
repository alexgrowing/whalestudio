import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearIteratePrimePowSubMemFiltration
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_iterate_prime_pow_sub_mem_filtration : ∀ (l : ℕ) [Fact l.Prime] (A N : Type) [CommRing A] [AddCommGroup N] [Module A N] (n : Ideal A) (γ : A →+* A) (Y : N →+ N), (∀ a x, Y (a • x) = γ a • Y x) → (∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1)) → (∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) → ∀ b : ℕ, 1 ≤ b → ∀ x, Y^[l ^ b] x - x ∈ (Ideal.span {((l : A)) ^ 2} ⊔ n ^ (l ^ (b - 1))) • (⊤ : Submodule A N) := by
  first | exact @GlobalTheory.semilinear_iterate_prime_pow_sub_mem | exact GlobalTheory.semilinear_iterate_prime_pow_sub_mem | (intros; apply GlobalTheory.semilinear_iterate_prime_pow_sub_mem <;> assumption)
