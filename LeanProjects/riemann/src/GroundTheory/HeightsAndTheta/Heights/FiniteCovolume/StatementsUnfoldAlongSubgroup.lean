import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal

noncomputable section

def UnfoldAlongSubgroup.Statement (G Y : Type*) [Group G] [MeasurableSpace G] [MeasurableSpace Y] :
    Prop :=
  ∀ (μ : Measure G) (H : Subgroup G) [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant]
    [SFinite ν] (ρ : Measure Y) [SFinite ρ] (s : Y → G),
    Measurable (fun p : H × Y => (p.1 : G) * s p.2) →
    (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ x, f (x * s y) ∂ν ∂ρ) →
    ∀ (Γ : Subgroup G) [Countable Γ], Γ ≤ H →
    ∀ (FD : Set G) (FD₀ : Set H), IsFundamentalDomain Γ FD μ →
      IsFundamentalDomain (Γ.subgroupOf H) FD₀ ν →
    ∀ f : G → ℝ≥0∞, Measurable f → (∀ x : H, ∀ g, f (x * g) = f g) →
      ∫⁻ g in FD, f g ∂μ = ν FD₀ * ∫⁻ y, f (s y) ∂ρ

section Inhabitants

theorem measurableSingletonClass_cyclicTwo : MeasurableSingletonClass C2 :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

attribute [local instance] measurableSingletonClass_cyclicTwo

abbrev topSubgroupCyclicTwo : Subgroup C2 := ⊤

instance : MeasurableMul topSubgroupCyclicTwo :=
  ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩

instance : (Measure.count : Measure topSubgroupCyclicTwo).IsMulLeftInvariant :=
  ⟨fun g => by
    ext s hs
    rw [Measure.map_apply (measurable_of_countable _) hs]
    have he : (fun x : topSubgroupCyclicTwo => g * x) ⁻¹' s = (fun x => g⁻¹ * x) '' s := by
      ext x
      simp
    rw [he, Measure.count_apply ((Set.to_countable _).measurableSet), Measure.count_apply hs]
    exact congrArg _ ((mul_right_injective (g⁻¹ : topSubgroupCyclicTwo)).injOn.encard_image)⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
