import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableZeroCount
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_zero_count : ∀ (d : ℕ) (α : Type) [Fintype α] (U A : Set (V d)) (b : α → V d → ℂ), (∀ j, ContinuousOn (b j) U) → A ⊆ U → IsSigmaCompact A → Measurable (zeroCnt d A b : (Fin d → α → ℂ) → ℝ≥0∞) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt | exact GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt <;> assumption)
