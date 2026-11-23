import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfCompactCoercive
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_of_isCompactOperator_coercive : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H), IsCompactOperator A → ∀ (S : Submodule ℂ H) (c : ℝ), 0 < c → (∀ u ∈ S, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) → FiniteDimensional ℂ S := by
  first | exact @GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive | exact GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive | (intros; apply GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive <;> assumption)
