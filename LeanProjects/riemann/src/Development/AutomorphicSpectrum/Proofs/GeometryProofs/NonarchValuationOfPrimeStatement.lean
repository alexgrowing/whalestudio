import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonarchValuationOfPrime
import Mathlib
open NumberField IsDedekindDomain UniqueFactorizationMonoid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonarch_valuation_of_prime : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (μ : R →*₀ ℝ) (a : R), a ≠ 0 → (∀ x, 0 ≤ μ x) → (∀ x, μ x ≤ 1) → (∀ x y, μ (x + y) ≤ max (μ x) (μ y)) → μ a < 1 → μ a ≠ 0 → ∃ (P : Ideal R) (c : ℝ), P.IsPrime ∧ P ≠ ⊥ ∧ a ∈ P ∧ 0 < c ∧ ∀ x : R, x ≠ 0 → μ x = c ^ (normalizedFactors (Ideal.span {x})).count P := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.map_eq_pow_count_of_ultrametric | exact GlobalTheory.CompanionTheory.Ggeo.map_eq_pow_count_of_ultrametric | (intros; apply GlobalTheory.CompanionTheory.Ggeo.map_eq_pow_count_of_ultrametric <;> assumption)
