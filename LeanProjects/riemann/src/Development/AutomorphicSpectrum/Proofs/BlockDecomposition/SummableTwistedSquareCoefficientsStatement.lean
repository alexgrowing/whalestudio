import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableTwistedSquareCoefficients
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_twisted_square_coefficients : ∀ (M N k : ℕ) [NeZero M] (hM : N ∣ M) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → (∀ n : ℕ, Nat.Coprime n N → ‖a (n ^ 2)‖ ≤ 2 * (n : ℝ) * (n : ℝ) ^ (k - 1)) → ∀ s : ℂ, 2 < s.re → LSeriesSummable (fun n : ℕ => DirichletCharacter.changeLevel hM χ⁻¹ (n : ZMod M) * a (n ^ 2)) (s + k - 1) := by
  first | exact @GlobalTheory.CompanionTheory.LSeriesBound.lseriesSummable_twist_squares | exact GlobalTheory.CompanionTheory.LSeriesBound.lseriesSummable_twist_squares | (intros; apply GlobalTheory.CompanionTheory.LSeriesBound.lseriesSummable_twist_squares <;> assumption)
