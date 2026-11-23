import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ImplicitRootAnalytic
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.implicit_root_analytic : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (n : ℕ) (c : ℕ → E → ℂ) (w₀ : E) (τ₀ : ℂ), (∀ j, AnalyticAt ℂ (c j) w₀) → ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j = 0 → ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) ≠ 0 → ∃ (V : Set E) (W : Set ℂ) (g : E → ℂ), IsOpen V ∧ w₀ ∈ V ∧ IsOpen W ∧ τ₀ ∈ W ∧ AnalyticOnNhd ℂ g V ∧ ∀ w ∈ V, ∀ τ ∈ W, ∑ j ∈ Finset.range (n + 1), c j w * τ ^ j = 0 → τ = g w := by
  first | exact @GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root | exact GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root | (intros; apply GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root <;> assumption)
