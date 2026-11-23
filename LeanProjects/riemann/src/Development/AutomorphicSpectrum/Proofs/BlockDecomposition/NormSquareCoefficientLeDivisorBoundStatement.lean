import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSquareCoefficientLeDivisorBound
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
open Ad3 Ad3.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_square_coefficient_le_divisor_bound : ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ), IsEig k N χ a → E2a → (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ α β : ℂ, α + β = a p ∧ α * β = χ p * (p : ℂ) ^ (k - 1) ∧ ‖α‖ = ‖β‖) → ∀ n : ℕ, Nat.Coprime n N → ‖a (n ^ 2)‖ ≤ (((n ^ 2).divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (k - 1) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeSq.norm_sq_le | exact GlobalTheory.CompanionTheory.HeckeSq.norm_sq_le | (intros; apply GlobalTheory.CompanionTheory.HeckeSq.norm_sq_le <;> assumption)
