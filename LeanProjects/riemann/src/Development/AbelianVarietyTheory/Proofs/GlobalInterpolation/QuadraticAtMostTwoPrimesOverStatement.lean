import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticAtMostTwoPrimesOver
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_field_at_most_two_primes_over_prime : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (q : ℕ), q.Prime → ∀ P₁ P₂ P₃ : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ P₁.asIdeal → ((q : ℕ) : 𝓞 K) ∈ P₂.asIdeal → ((q : ℕ) : 𝓞 K) ∈ P₃.asIdeal → P₁ = P₂ ∨ P₁ = P₃ ∨ P₂ = P₃ := by
  first | exact @GlobalTheory.quadratic_at_most_two_primes_over | exact GlobalTheory.quadratic_at_most_two_primes_over | (intros; apply GlobalTheory.quadratic_at_most_two_primes_over <;> assumption)
