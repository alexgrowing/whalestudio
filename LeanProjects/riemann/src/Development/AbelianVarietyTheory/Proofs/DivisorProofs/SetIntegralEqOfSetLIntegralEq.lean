import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularAndLintegralUnfoldOfLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSetOfSmulMemEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMulMeasureInterSmulPreimageOfInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalDomainUnfoldRefoldMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSmulPreimageFundamentalDomainEqStatement
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep
variable {S X : Type} [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X]
  [MeasurableSMul₂ S X]

theorem measure_mul_setLIntegral_eq [MeasurableInv S] (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] (D : Set X) (hD : MeasurableSet D) (E : Set S)
    (hE : MeasurableSet E) (ψ : X → ℝ≥0∞) (hψ : Measurable ψ)
    (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ν E * ∫⁻ x in D, ψ x ∂μ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ :=
  GlobalTheory.T.lintegral_mul_measure_inter_smul_preimage_of_invariant S X ν μ D hD E hE ψ hψ hinv

theorem lintegral_unfold_eq [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν]
    [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D₁ D₂ : Set X) (hD₁ : MeasurableSet D₁)
    (hD₂ : IsFundamentalDomain Γ D₂ μ) (E : Set S) (hE : MeasurableSet E)
    (hEf : IsFundamentalDomain Γ E ν) (ψ : X → ℝ≥0∞) (hψ : Measurable ψ)
    (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) ∂μ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ :=
  GlobalTheory.T.lintegral_fundamentalDomain_unfold_refold_measure S X ν μ Γ D₁ D₂ hD₁ hD₂ E hE hEf ψ hψ hinv

theorem ae_measure_setOf_smul_mem_eq [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν]
    [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D : Set X) (hD : MeasurableSet D)
    (hDf : IsFundamentalDomain Γ D μ) (E : Set S) (hE : IsFundamentalDomain Γ E ν) :
    ∀ᵐ y ∂μ, ν {s | s • y ∈ D} = ν E :=
  GlobalTheory.T.ae_measure_smul_preimage_fundamentalDomain_eq S X ν μ Γ D hD hDf E hE

theorem lintegral_mul_eq_of_measurable [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] (Γ₁ Γ₂ : Subgroup S) [Countable Γ₁] [Countable Γ₂]
    (D₁ D₂ : Set X) (E₁ E₂ : Set S) (hD₁m : MeasurableSet D₁) (hD₂m : MeasurableSet D₂)
    (hE₂m : MeasurableSet E₂)
    (hD₁ : IsFundamentalDomain Γ₁ D₁ μ) (hD₂ : IsFundamentalDomain Γ₂ D₂ μ)
    (hE₁ : IsFundamentalDomain Γ₁ E₁ ν) (hE₂ : IsFundamentalDomain Γ₂ E₂ ν)
    (ψ : X → ℝ≥0∞) (hψ : Measurable ψ) (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ν E₂ * ∫⁻ x in D₁, ψ x ∂μ = ν E₁ * ∫⁻ x in D₂, ψ x ∂μ := by
  rw [measure_mul_setLIntegral_eq ν μ D₁ hD₁m E₂ hE₂m ψ hψ hinv,
    lintegral_unfold_eq ν μ Γ₂ D₁ D₂ hD₁m hD₂ E₂ hE₂m hE₂ ψ hψ hinv, ← lintegral_const_mul _ hψ]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [ae_measure_setOf_smul_mem_eq ν μ Γ₁ D₁ hD₁m hD₁ E₁ hE₁] with y hy
  have : ν {s : S | s⁻¹ • y ∈ D₁} = ν {s : S | s • y ∈ D₁} := by
    change ν ({s : S | s • y ∈ D₁}⁻¹) = _
    exact Measure.measure_inv (μ := ν) _
  rw [this, hy, mul_comm]
end GlobalTheory.CovolIndep

namespace GlobalTheory.CovolIndep
variable {S X : Type} [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X]
  [MeasurableSMul₂ S X]

theorem lintegral_mul_eq [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] (Γ₁ Γ₂ : Subgroup S) [Countable Γ₁] [Countable Γ₂]
    (D₁ D₂ : Set X) (E₁ E₂ : Set S)
    (hD₁ : IsFundamentalDomain Γ₁ D₁ μ) (hD₂ : IsFundamentalDomain Γ₂ D₂ μ)
    (hE₁ : IsFundamentalDomain Γ₁ E₁ ν) (hE₂ : IsFundamentalDomain Γ₂ E₂ ν)
    (ψ : X → ℝ≥0∞) (hψ : Measurable ψ) (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ν E₂ * ∫⁻ x in D₁, ψ x ∂μ = ν E₁ * ∫⁻ x in D₂, ψ x ∂μ := by
  have a₁ := hD₁.nullMeasurableSet.toMeasurable_ae_eq
  have a₂ := hD₂.nullMeasurableSet.toMeasurable_ae_eq
  have b₂ := hE₂.nullMeasurableSet.toMeasurable_ae_eq
  have key := lintegral_mul_eq_of_measurable ν μ Γ₁ Γ₂ (toMeasurable μ D₁) (toMeasurable μ D₂)
    E₁ (toMeasurable ν E₂) (measurableSet_toMeasurable _ _) (measurableSet_toMeasurable _ _)
    (measurableSet_toMeasurable _ _) (isFundamentalDomain_of_ae_eq hD₁ a₁)
    (isFundamentalDomain_of_ae_eq hD₂ a₂) hE₁ (isFundamentalDomain_of_ae_eq hE₂ b₂) ψ hψ hinv
  rwa [measure_toMeasurable, setLIntegral_congr a₁, setLIntegral_congr a₂] at key

end GlobalTheory.CovolIndep

namespace GlobalTheory

end GlobalTheory
