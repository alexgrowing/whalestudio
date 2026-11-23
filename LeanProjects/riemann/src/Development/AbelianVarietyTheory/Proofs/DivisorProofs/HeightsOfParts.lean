import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundLogRatioHalfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundLogRatioUnitStatement
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
open scoped ComplexOrder

namespace GlobalTheory.Mean4

theorem heights_of_parts : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (A : SlopeTestRemainingChoices Y), ∀ (inner : Y.Pt → Prop) (hF hA : Y.Pt → ℝ), (∀ c₀ : ℝ, 0 < c₀ → ∃ t₀ : ℝ, 0 < t₀ ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt Y) (t : ℚ), IsRat Y u → supAbs Y u ≤ 1 → 0 < t → (t : ℝ) ≤ t₀ → (∀ τ, (t : ℝ) ≤ gap Y u τ) → CptGaps Y c₀ u → (∀ y, inner y → (t : ℝ) / 4 * max (hF y) 0 - C * Real.log (2 + max (hF y) 0) - C * Real.log B - C ≤ A.ht (Y.Mbar B u (t ^ 2)) y) ∧ (∀ y, ¬ inner y → -C ≤ hA y ∧ (t : ℝ) ^ 2 * hA y - C * Real.log (2 + C + hA y) - C * Real.log (B / (t : ℝ) ^ 2) - C ≤ A.ht (Y.Mbar B u (t ^ 2)) y) ∧ ∀ c, ∃ Z, A.dense c Z ∧ ∀ y ∈ Z, A.ht (Y.Mbar B u (t ^ 2)) y ≤ C * Real.log B + C) → Heights A := by
  intro D Y A inner hF hA H c₀ hc₀
  obtain ⟨t₀, ht₀, C, hC, H⟩ := H c₀ hc₀
  obtain ⟨C₁, h₁⟩ := GlobalTheory.T.lower_bound_log_ratio_half C
  obtain ⟨C₂, h₂⟩ := GlobalTheory.T.lower_bound_log_ratio_unit C hC
  refine ⟨min t₀ (1 / 2), lt_min ht₀ (by norm_num), max (max C₁ C₂) (3 * C), ?_⟩
  intro B hB u t hu hs ht htt hg hcp _
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hth : (t : ℝ) ≤ 1 / 2 := htt.trans (min_le_right _ _)
  obtain ⟨Hi, Hb, Hd⟩ := H B hB u t hu hs ht (htt.trans (min_le_left _ _)) hg hcp
  have hs0 : (0 : ℝ) < (t : ℝ) ^ 2 := by positivity
  have hs1 : (t : ℝ) ^ 2 ≤ 1 := by nlinarith
  have hlog : 0 ≤ Real.log (B / (t : ℝ) ^ 2) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hs0]
    linarith
  have hlB : (1 : ℝ) / 2 ≤ Real.log B := by
    have := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hB
    linarith
  refine ⟨fun y => ?_, fun c => ?_⟩
  · by_cases hy : inner y
    · have := h₁ B t _ _ hB htR hth (le_max_right (hF y) 0) (Hi y hy)
      have hle : C₁ ≤ max (max C₁ C₂) (3 * C) := (le_max_left _ _).trans (le_max_left _ _)
      have := mul_le_mul_of_nonneg_right hle hlog
      linarith
    · have := h₂ B _ _ _ hB hs0 hs1 (Hb y hy).1 (Hb y hy).2
      have hle : C₂ ≤ max (max C₁ C₂) (3 * C) := (le_max_right _ _).trans (le_max_left _ _)
      have := mul_le_mul_of_nonneg_right hle hlog
      linarith
  · obtain ⟨Z, hZ, hZ'⟩ := Hd c
    refine ⟨Z, hZ, fun y hy => (hZ' y hy).trans ?_⟩
    have hle : 3 * C ≤ max (max C₁ C₂) (3 * C) := le_max_right _ _
    have := mul_le_mul_of_nonneg_right hle (by linarith : 0 ≤ Real.log B)
    nlinarith

end GlobalTheory.Mean4
