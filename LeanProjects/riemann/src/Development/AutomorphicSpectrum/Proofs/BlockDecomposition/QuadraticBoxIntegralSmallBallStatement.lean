import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBoxIntegralSmallBall
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoreR
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_box_integral_small_ball : ∀ (P ι : Type) [Fintype P] [Fintype ι] (a : ℕ), 0 < a → ∀ (Q : (P → ι → ℝ) → (P → ℝ)), Measurable Q → ∀ C : ℝ≥0, (∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U → (volume : Measure (P → ι → ℝ)) (Q ⁻¹' U ∩ boxR t) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ a) * volume U) → ∀ f : (P → ι → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ N : ℕ, ∃ C' : ℝ, ∀ x, f x * (1 + ∑ w, ‖x w‖) ^ N ≤ C') → ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ U : Set (P → ℝ), MeasurableSet U → ∫⁻ x in Q ⁻¹' U ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x) ≤ ENNReal.ofReal ε * volume U := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.tail_small | exact GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.tail_small | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.tail_small <;> assumption)
