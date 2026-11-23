import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvLeOfSupportCompact
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_inv_le_of_support_compact_alt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ φ : H → ENNReal, Measurable φ → (∀ x ∉ K, φ x = 0) → ∫⁻ x, φ x⁻¹ ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by
  first | exact @GlobalTheory.lintegral_inv_le_of_support_compact | exact GlobalTheory.lintegral_inv_le_of_support_compact | (intros; apply GlobalTheory.lintegral_inv_le_of_support_compact <;> assumption)
