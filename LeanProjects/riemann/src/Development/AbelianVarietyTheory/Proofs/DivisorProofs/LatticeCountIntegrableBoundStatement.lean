import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCountIntegrableBound
import Mathlib
open scoped NNReal ENNReal
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_count_integrable_bound : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] (φ h : G → ℝ≥0∞), Measurable φ →
    ∫⁻ g, φ g ∂μ ≠ ⊤ → ∀ (T : ℕ → Finset G) (c : ℕ) (t : ℝ), (∀ m, 0 < m → (T m).card ≤ m ^ c) → (c : ℝ) + 1 < t →
    (∀ g, ∃ m, 0 < m ∧ ∃ x ∈ T m, h g ≤ (m : ℝ≥0∞) ^ (-t) * φ (x⁻¹ * g)) → ∫⁻ g, h g ∂μ ≠ ⊤ := by
  first | exact @GlobalTheory.lintegral_ne_top_of_le_rpow_mul_translate | exact GlobalTheory.lintegral_ne_top_of_le_rpow_mul_translate | (intros; apply GlobalTheory.lintegral_ne_top_of_le_rpow_mul_translate <;> assumption)
