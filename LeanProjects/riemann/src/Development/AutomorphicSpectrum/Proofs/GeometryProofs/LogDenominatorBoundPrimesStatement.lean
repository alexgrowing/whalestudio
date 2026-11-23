import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogDenominatorBoundPrimes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_denominator_bound_primes : ∀ (S : Finset ℕ) (m₀ : ℕ), (∀ p ∈ S, p.Prime) → 0 < m₀ → ∃ q m : ℕ, 0 < q ∧ 0 < m ∧ Real.log m ≤ q * (Real.log m₀ + ∑ p ∈ S, (if p = 2 then 2 else 1 / ((p : ℝ) - 1)) * Real.log p) ∧ ∀ (Ω : Type) [Field Ω] [CharZero Ω] (W : ValuationSubring Ω) (κ : Ω), (κ = 1 ∨ ∃ p ∈ S, HT.IsCp p κ) → ∀ t : Ω, ((m₀ : Ω) * κ) * t ∈ W → (m : Ω) * t ^ q ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ClearConstants.clear_constants | exact GlobalTheory.CompanionTheory.Ar.ClearConstants.clear_constants | (intros; apply GlobalTheory.CompanionTheory.Ar.ClearConstants.clear_constants <;> assumption)
