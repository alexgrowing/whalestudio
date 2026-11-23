import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedFormComparisonPosSemidef
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_form_comparison_posSemidef : ∀ (n : ℕ) (B B₀ : Matrix (Fin n) (Fin n) ℂ) (s r R κ C : ℝ), B.PosDef → B₀.PosDef → 1 ≤ r → r ≤ Real.sqrt R → 2 ≤ R → 0 ≤ C → 2 * C + 2 < κ → s ∈ Set.Icc (0 : ℝ) 1 → 1 - s ≤ (r / R) ^ κ → (((r ^ C : ℝ) : ℂ) • B₀ - B).PosSemidef → (((r ^ C : ℝ) : ℂ) • B - B₀).PosSemidef → ((((1 - R⁻¹)⁻¹ : ℝ) : ℂ) • B - GlobalTheory.GradedNorm.mix s B₀ B).PosSemidef ∧ ((((1 - R⁻¹)⁻¹ : ℝ) : ℂ) • GlobalTheory.GradedNorm.mix s B₀ B - B).PosSemidef ∧ ((((1 - R⁻¹)⁻¹ : ℝ) : ℂ) • B - GlobalTheory.GradedNorm.mixDual s B₀ B).PosSemidef ∧ ((((1 - R⁻¹)⁻¹ : ℝ) : ℂ) • GlobalTheory.GradedNorm.mixDual s B₀ B - B).PosSemidef := by
  first | exact @GlobalTheory.GradedNorm.interp_comparable | exact GlobalTheory.GradedNorm.interp_comparable | (intros; apply GlobalTheory.GradedNorm.interp_comparable <;> assumption)
