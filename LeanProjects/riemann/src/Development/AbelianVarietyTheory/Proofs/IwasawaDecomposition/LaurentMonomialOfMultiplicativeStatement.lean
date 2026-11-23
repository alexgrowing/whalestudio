import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LaurentMonomialOfMultiplicative
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monomial_of_multiplicative_of_single_eq_zpow : ∀ (n : ℕ) (χ : (Fin n → ℂ) → ℂ), χ 1 = 1 → (∀ s t : Fin n → ℂ, (∀ i, s i ≠ 0) → (∀ i, t i ≠ 0) → χ (s * t) = χ s * χ t) → (∀ i : Fin n, ∃ k : ℤ, ∀ t : ℂ, t ≠ 0 → χ (Pi.mulSingle i t) = t ^ k) → ∃ μ : Fin n → ℤ, ∀ d : Fin n → ℂ, (∀ i, d i ≠ 0) → χ d = ∏ i, d i ^ μ i := by
  first | exact @GlobalTheory.laurentMonomial_of_multiplicative | exact GlobalTheory.laurentMonomial_of_multiplicative | (intros; apply GlobalTheory.laurentMonomial_of_multiplicative <;> assumption)
