import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.PushAFinsumInter
import ReciprocityTheory.AnalyticForms.PotentialTheory.PushBForward

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

def PushLocalStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) → ∀ (q : X → Fin e → ℂ) (V : Set X),
    IsOpen V → Set.InjOn q V → (∀ i, A.HoloOn V (fun x => q x i)) →
    (∀ x ∈ V, ∀ j, x ∈ (A.chart j).source →
      LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) →
    ∀ g : X → ℝ, tsupport g ⊆ V → MIntegrable A Φ g →
      mInt A Φ g = ∫ y in q '' V, ∑ᶠ x ∈ q ⁻¹' {y} ∩ V, g x * pushDens A Φ q x

theorem pushForward : PushForwardStatement := pushB_forward

end

end ReciprocityTheory.AnForm.M
