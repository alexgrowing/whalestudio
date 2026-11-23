import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjEisensteinPolynomialLevelOneStatement

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem isobaric_monomial_div (c x y ω : ℂ) (a b w : ℕ) (h : 4 * a + 6 * b = w) :
    c * (x ^ a * y ^ b) / ω ^ w = c * ((x / ω ^ 4) ^ a * (y / ω ^ 6) ^ b) := by
  rw [div_pow, div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm, ← pow_add, h, mul_div_assoc]

theorem levelOne_value_transport : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → QConj g N F F' → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → g (F τ₀ / ω₀ ^ w) = F' τ₁ / ω₁ ^ w := by
  intro g w N F F' τ₀ τ₁ ω₀ ω₁ hN hF hq h4 h6
  obtain ⟨s, c, hs, h0, h1⟩ := GlobalTheory.T.exists_conj_eisensteinPolynomial_levelOne g w N F F' hN hF hq
  rw [h0, h1, Finset.sum_div, Finset.sum_div, map_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [isobaric_monomial_div _ _ _ _ _ _ _ (hs p hp), isobaric_monomial_div _ _ _ _ _ _ _ (hs p hp),
    map_mul, map_mul, map_pow, map_pow, h4, h6]

end GlobalTheory.QFam
