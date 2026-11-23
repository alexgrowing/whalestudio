import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueSumHyperplaneZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_sum_hyperplane_zero : ∀ {k : ℕ} {J K : Type} [DecidableEq K] (s : Finset J) (m : J → Finset K) (v : J → K → A0 k) (g : J → A0 k → ℂ),
  (∀ j ∈ s, ContDiff ℝ ∞ (g j)) → (∀ j ∈ s, ∀ a ∈ m j, v j a ≠ 0) →
  (∀ j ∈ s, ∀ a ∈ m j, ∀ a' ∈ m j, a ≠ a' → ∀ r : ℝ, v j a' ≠ r • v j a) →
  (∀ b : A0 k, b ≠ 0 → ∀ x : A0 k, ⟪x, b⟫_ℝ = 0 → (∀ j ∈ s, ∀ a ∈ m j, (∀ r : ℝ, v j a ≠ r • b) → ⟪x, v j a⟫_ℝ ≠ 0) →
    ∑ j ∈ s, ∑ a ∈ (m j).filter (fun a => ∃ r : ℝ, v j a = r • b),
      g j x * ((⟪v j a, b⟫_ℝ : ℂ)⁻¹ * ∏ a' ∈ (m j).erase a, (⟪x, v j a'⟫_ℝ : ℂ)⁻¹) = 0) →
  ∃ F : A0 k → ℂ, ContDiff ℝ ∞ F ∧ ∀ x, (∀ j ∈ s, ∀ a ∈ m j, ⟪x, v j a⟫_ℝ ≠ 0) →
    F x = ∑ j ∈ s, g j x * ∏ a ∈ m j, (⟪x, v j a⟫_ℝ : ℂ)⁻¹ := by
  first | exact @GlobalTheory.smooth_extension_of_residues_cancel | exact GlobalTheory.smooth_extension_of_residues_cancel | (intros; apply GlobalTheory.smooth_extension_of_residues_cancel <;> assumption)
