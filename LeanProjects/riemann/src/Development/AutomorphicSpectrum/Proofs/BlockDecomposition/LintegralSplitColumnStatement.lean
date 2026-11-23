import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralSplitColumn
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_split_column : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (Φ : (Fin d → α → ℂ) → ℝ≥0∞), Measurable Φ → ∫⁻ C : Fin d → α → ℂ, Φ C = ∫⁻ C' : Fin d → {j : α // j ≠ j₀} → ℂ, ∫⁻ c : Fin d → ℂ, Φ (joinCol j₀ c C') := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.lintegral_joinCol | exact GlobalTheory.CompanionTheory.FSCrofton.lintegral_joinCol | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.lintegral_joinCol <;> assumption)
