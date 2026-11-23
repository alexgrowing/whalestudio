import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyProductPartialSumsDvdPow
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cauchy_product_partial_sums_dvd_pow : ∀ {R : Type} [CommRing R] (x : R) (α β : ℕ → R) (A B : R), (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A - ∑ p ∈ Finset.range n, α p) → (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ B - ∑ q ∈ Finset.range n, β q) → ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) := by
  first | exact @GlobalTheory.cauchy_product_dvd_pow | exact GlobalTheory.cauchy_product_dvd_pow | (intros; apply GlobalTheory.cauchy_product_dvd_pow <;> assumption)
