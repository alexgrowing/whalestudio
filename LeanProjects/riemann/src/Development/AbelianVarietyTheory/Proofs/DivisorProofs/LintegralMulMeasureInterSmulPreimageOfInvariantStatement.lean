import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMulMeasureInterSmulPreimageOfInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSetOfSmulMemEqZero
open MeasureTheory
open scoped ENNReal Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_mul_measure_inter_smul_preimage_of_invariant : ∀ (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X] [MeasurableSMul₂ S X] [MeasurableInv S] (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ] (D : Set X), MeasurableSet D → ∀ (E : Set S), MeasurableSet E → ∀ (ψ : X → ℝ≥0∞), Measurable ψ → (∀ (s : S) (x : X), ψ (s • x) = ψ x) → ν E * ∫⁻ x in D, ψ x ∂μ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ := by
  first | exact @GlobalTheory.lintegral_mul_measure_inter_smul_preimage | exact GlobalTheory.lintegral_mul_measure_inter_smul_preimage | (intros; apply GlobalTheory.lintegral_mul_measure_inter_smul_preimage <;> assumption)
