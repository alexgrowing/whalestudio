import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSubgroupCountableAndExistsStrictFundamen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.QuotFubini

theorem existsUnique_mul_mem {G : Type} [Group G] {Γ R : Subgroup G} (hΓ : Γ ≤ R) {S : Set G}
    (hS : ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ S) (h : G) (r : R) :
    ∃! γ : Γ.subgroupOf R, γ • r ∈ {r : R | (r : G) * h ∈ S} := by
  obtain ⟨γ, h1, h2⟩ := hS ((r : G) * h)
  refine ⟨⟨⟨γ, hΓ γ.2⟩, γ.2⟩, ?_, fun δ hδ => ?_⟩
  · change ((γ : G) * r) * h ∈ S
    rw [mul_assoc]; exact h1
  · have h3 : (⟨((δ : R) : G), δ.2⟩ : Γ) = γ := by
      refine h2 _ ?_
      have : (((δ : R) : G) * r) * h ∈ S := hδ
      rw [mul_assoc] at this
      exact this
    ext
    exact congrArg (fun x : Γ => (x : G)) h3

end GlobalTheory.QuotFubini

namespace GlobalTheory

open GlobalTheory.QuotFubini in

theorem quot_fubini_mean : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (R Γ : Subgroup G), Γ ≤ R → IsClosed (R : Set G) → Countable Γ → DiscreteTopology Γ → ∀ (μR : Measure R), μR.IsHaarMeasure → ∀ (𝓡 : Set R) (𝓑 : Set G), IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR → IsFundamentalDomain Γ 𝓑 μ → ∀ f : G → ℂ, Measurable f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓑 μ → (∀ h, IntegrableOn (fun r : R => f (r * h)) 𝓡 μR) → IsQuotIntL1 μR μ (fun h => ∫ r in 𝓡, f ((r : G) * h) ∂μR) (∫ g in 𝓑, f g ∂μ) := by
  intro G _ _ _ _ _ _ _ _ μ _ R Γ hΓR hR hΓc hΓd μR hμR 𝓡 𝓑 h𝓡 h𝓑 f hf hfΓ hf𝓑 hf𝓡
  obtain ⟨-, S, hSm, hS⟩ := GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain Γ
  have : Countable (Γ.subgroupOf R) :=
    (Subgroup.subgroupOfEquivOfLe hΓR).toEquiv.countable_iff.2 inferInstance
  have hSfd : IsFundamentalDomain Γ S μ := IsFundamentalDomain.mk' hSm.nullMeasurableSet hS
  have hfΓ' : ∀ (γ : Γ) (x : G), f (γ • x) = f x := fun γ x => hfΓ γ γ.2 x
  have hmh : ∀ h : G, Measurable (fun r : R => (r : G) * h) := fun h =>
    (continuous_subtype_val.mul continuous_const).measurable
  have hSh : ∀ h : G, MeasurableSet {r : R | (r : G) * h ∈ S} := fun h => hmh h hSm
  have hShfd : ∀ h : G, IsFundamentalDomain (Γ.subgroupOf R) {r : R | (r : G) * h ∈ S} μR := fun h =>
    IsFundamentalDomain.mk' (hSh h).nullMeasurableSet (existsUnique_mul_mem hΓR hS h)
  have hfR : ∀ h : G, ∀ (γ : Γ.subgroupOf R) (r : R), f (((γ • r : R) : G) * h) = f ((r : G) * h) := by
    intro h γ r
    change f ((((γ : R) : G) * r) * h) = _
    rw [mul_assoc]; exact hfΓ _ γ.2 _
  have hind : ∀ h : G, (fun r : R => S.indicator f ((r : G) * h)) =
      {r : R | (r : G) * h ∈ S}.indicator (fun r : R => f ((r : G) * h)) := by
    intro h; ext r
    by_cases hr : (r : G) * h ∈ S
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem (show r ∈ {r : R | (r : G) * h ∈ S} from hr)]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem (show r ∉ {r : R | (r : G) * h ∈ S} from hr)]
  refine ⟨S.indicator f, ?_, fun h => ?_, fun h => ?_, ?_⟩
  · exact (integrable_indicator_iff hSm).2 ((hSfd.integrableOn_iff h𝓑 hfΓ').2 hf𝓑)
  · rw [hind h]
    exact (integrable_indicator_iff (hSh h)).2 (((hShfd h).integrableOn_iff h𝓡 (hfR h)).2 (hf𝓡 h))
  · rw [hind h, integral_indicator (hSh h)]
    exact (h𝓡.setIntegral_eq (hShfd h) (hfR h))
  · rw [integral_indicator hSm]
    exact h𝓑.setIntegral_eq hSfd hfΓ'

end GlobalTheory
