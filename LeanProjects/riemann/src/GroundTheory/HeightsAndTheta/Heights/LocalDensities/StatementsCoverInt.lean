import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

def CoverChartLIntegral.Hyp {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (q : X → Fin e → ℂ) (M₀ : Set X) (Δ : Set (Fin e → ℂ)) (d : ℕ) : Prop :=
  IsOpen M₀ ∧ (∀ i, A.HoloOn M₀ fun x => q x i) ∧ IsClosed Δ ∧
    (∃ h : Set.MapsTo q M₀ Δᶜ, IsCoveringMap h.restrict) ∧
    ∀ z ∉ Δ, (M₀ ∩ q ⁻¹' {z}).encard = d

def CoverChartLIntegral.Statement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] (A : FinHolAtlas e X)
    (χ : ChartPartition A) (q : X → Fin e → ℂ) (M₀ : Set X) (Δ : Set (Fin e → ℂ)) (d : ℕ),
    CoverChartLIntegral.Hyp A q M₀ Δ d → ∀ g : (Fin e → ℂ) → ENNReal, Measurable g →
      ∑ j, ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀,
          ENNReal.ofReal (χ.χ j ((A.chart j).symm y)) *
            ENNReal.ofReal (‖LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) y :
              (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2) * g (q ((A.chart j).symm y)) =
        d * ∫⁻ z in Δᶜ, g z

section Examples

def linePartitionOne : ChartPartition lineAtlas where
  χ _ _ := 1
  smooth _ _ := contDiffOn_const
  nonneg _ _ := zero_le_one
  tsupport_subset _ := fun _ _ => Set.mem_univ _
  sum_eq_one _ := by show ∑ _j : Fin 1, (1 : ℝ) = 1; simp

end Examples

end

end GroundTheory.Heights₂.Heights.FourB
