import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalDomainUnfoldRefoldMeasure
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSetOfSmulMemEqZero
open MeasureTheory
open scoped ENNReal Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_fundamentalDomain_unfold_refold_measure : ∀ (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X] [MeasurableSMul₂ S X] [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν] [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ] (Γ : Subgroup S) [Countable Γ] (D₁ D₂ : Set X), MeasurableSet D₁ → IsFundamentalDomain Γ D₂ μ → ∀ (E : Set S), MeasurableSet E → IsFundamentalDomain Γ E ν → ∀ (ψ : X → ℝ≥0∞), Measurable ψ → (∀ (s : S) (x : X), ψ (s • x) = ψ x) → ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) ∂μ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ := by
  first | exact @GlobalTheory.CovolIndep.lintegral_unfold_refold | exact GlobalTheory.CovolIndep.lintegral_unfold_refold | (intros; apply GlobalTheory.CovolIndep.lintegral_unfold_refold <;> assumption)
