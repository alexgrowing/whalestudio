import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVecFixGroup

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def HaarParabolicCoordinates.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure] (x₀ : W), x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 →
    ∃ (ν : Measure (vecFixGroup h v x₀)) (κ : Measure M.stab)
      (τ : (InfinitePlace E → ℂ) → archUnitary h v),
      ν.IsHaarMeasure ∧ κ.IsHaarMeasure ∧ IsProbabilityMeasure κ ∧ Measurable τ ∧
      (∀ b : InfinitePlace E → ℂ, (∀ w, b w ≠ 0) →
        invApply (τ b) (vecAt v x₀) = fun w => b w • vecAt v x₀ w) ∧
      ∀ f : archUnitary h v → ℝ≥0∞, Measurable f →
        ∫⁻ g, f g ∂μ = ∫⁻ b : InfinitePlace E → ℂ, (∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))) *
          ∫⁻ k : M.stab, ∫⁻ x : vecFixGroup h v x₀, f (x * (τ b * k)) ∂ν ∂κ

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
