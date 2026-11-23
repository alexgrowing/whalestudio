import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumAddInvLeOfConsecutiveRatioBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_add_inv_le_of_consecutiveRatio_bounds : ∀ (a : ℕ) (t c₁ c₂ : ℝ), 0 < t → 0 < c₁ → ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → c₁ ≤ ∏ i, r i → ∏ i, r i ≤ c₂ → ∀ ρ : ℝ, 1 ≤ ρ → (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) → ∑ i, (r i + (r i)⁻¹) ≤ C * ρ ^ K := by
  first | exact @GlobalTheory.RatioIneq.sum_add_inv_le_of_ratio_bounds | exact GlobalTheory.RatioIneq.sum_add_inv_le_of_ratio_bounds | (intros; apply GlobalTheory.RatioIneq.sum_add_inv_le_of_ratio_bounds <;> assumption)
