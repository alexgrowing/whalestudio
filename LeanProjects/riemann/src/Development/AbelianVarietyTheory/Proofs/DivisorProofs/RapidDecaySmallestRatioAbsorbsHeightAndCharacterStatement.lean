import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RapidDecaySmallestRatioAbsorbsHeightAndCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rapidDecay_smallestRatio_absorbs_height_and_character : ∀ (a : ℕ) (t : ℝ), 0 < t → ∀ (lam : Fin a → ℝ) (N : ℕ), ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i ∨ ∃ i j : Fin a, (j : ℕ) = i + 1 ∧ (r j / r i) ^ m * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i := by
  first | exact @GlobalTheory.rapidDecay_real | exact GlobalTheory.rapidDecay_real | (intros; apply GlobalTheory.rapidDecay_real <;> assumption)
