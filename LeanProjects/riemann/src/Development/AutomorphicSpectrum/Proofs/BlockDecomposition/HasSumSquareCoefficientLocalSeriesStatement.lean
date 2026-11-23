import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSumSquareCoefficientLocalSeries
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
open Ad3 Ad3.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_square_coefficient_local_series : E2a → E2b → ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ), IsEig k N χ a → 1 ≤ k → ∀ p : ℕ, p.Prime → ∀ α β y s : ℂ, α ≠ 0 → β ≠ 0 → α + β = a p → α * β = χ p * (p : ℂ) ^ (k - 1) → ‖α / β‖ = 1 → ‖y‖ ≤ 1 → 0 < s.re → HasSum (fun j : ℕ => (χ p)⁻¹ ^ j * a (p ^ (2 * j)) * (y * (p : ℂ) ^ (-(s + k - 1))) ^ j) ((1 - (y * (p : ℂ) ^ (-s)) ^ 2) * ((1 - α / β * (y * (p : ℂ) ^ (-s)))⁻¹ * (1 - y * (p : ℂ) ^ (-s))⁻¹ * (1 - (α / β)⁻¹ * (y * (p : ℂ) ^ (-s)))⁻¹)) := by
  first | exact @GlobalTheory.CompanionTheory.LocalSeries.good_prime_local_series | exact GlobalTheory.CompanionTheory.LocalSeries.good_prime_local_series | (intros; apply GlobalTheory.CompanionTheory.LocalSeries.good_prime_local_series <;> assumption)
