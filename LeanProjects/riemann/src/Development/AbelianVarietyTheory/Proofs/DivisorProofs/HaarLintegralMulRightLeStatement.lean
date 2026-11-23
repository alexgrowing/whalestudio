import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarLintegralMulRightLe
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_lintegral_mul_right_le_alt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ y ∈ K, ∀ φ : H → ENNReal, Measurable φ → ∫⁻ x, φ (x * y) ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by
  first | exact @GlobalTheory.haar_lintegral_mul_right_le | exact GlobalTheory.haar_lintegral_mul_right_le | (intros; apply GlobalTheory.haar_lintegral_mul_right_le <;> assumption)
