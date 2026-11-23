import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RandomSectionZeroCount
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianDetLeviIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogFubiniStudyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogDehomogeniseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableZeroCountStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChangeVariablesZeroCountStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralSplitColumnStatement
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.random_section_zero_count : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U A : Set (V d)) (b : α → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (b j) U) → (∀ z ∈ U, b j₀ z ≠ 0) → A ⊆ U → IsSigmaCompact A → ∫⁻ C : Fin d → α → ℂ, gW d α C * zeroCnt d A b C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) * ∫⁻ z in A, ENNReal.ofReal ((d.factorial : ℝ) / Real.pi ^ d * (cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z).det.re) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.crofton_local | exact GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.crofton_local | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.crofton_local <;> assumption)
