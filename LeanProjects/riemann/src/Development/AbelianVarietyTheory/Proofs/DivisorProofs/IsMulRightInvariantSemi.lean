import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactLatticeUnitCovolume

open MeasureTheory GlobalTheory.Unf.SemiFd
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SemiMean

variable {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [LocallyCompactSpace K]
  [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

theorem isClosed_of_cocompact (Γ N : Subgroup G) [DiscreteTopology Γ]
    (hc : ∃ C : Set N, IsCompact C ∧ ∀ n : N, ∃ γ ∈ Γ.subgroupOf N, γ * n ∈ C) : IsClosed (N : Set G) := by
  obtain ⟨C, hC, hs⟩ := hc
  haveI : DiscreteTopology (Γ ⊓ N : Subgroup G) :=
    DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion (inf_le_left : Γ ⊓ N ≤ Γ))
      (Continuous.subtype_mk continuous_subtype_val _) (Subgroup.inclusion_injective _)
  have h1 : IsClosed ((Γ ⊓ N : Subgroup G) : Set G) := Subgroup.isClosed_of_discrete
  have h2 : (N : Set G) = ((Γ ⊓ N : Subgroup G) : Set G) * (Subtype.val '' C) := by
    ext x
    constructor
    · intro hx
      obtain ⟨γ, hγ, hk⟩ := hs ⟨x, hx⟩
      refine ⟨γ.1⁻¹, inv_mem (Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hγ, γ.2⟩), _, ⟨_, hk, rfl⟩, ?_⟩
      simp
    · rintro ⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩
      exact mul_mem (Subgroup.mem_inf.1 hγ).2 k.2
  rw [h2]
  exact h1.mul_right_of_isCompact (hC.image continuous_subtype_val)

theorem exists_mass_one (Γ N : Subgroup G) [DiscreteTopology Γ] [Countable Γ]
    (hc : ∃ C : Set N, IsCompact C ∧ ∀ n : N, ∃ γ ∈ Γ.subgroupOf N, γ * n ∈ C) :
    ∃ (ν : Measure N) (𝓝 : Set N), ν.IsHaarMeasure ∧ IsFundamentalDomain (Γ.subgroupOf N) 𝓝 ν ∧ ν 𝓝 = 1 := by
  haveI : LocallyCompactSpace N := (isClosed_of_cocompact Γ N hc).locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  let j : Γ.subgroupOf N → Γ := fun g => ⟨g.1.1, g.2⟩
  have hj : Function.Injective j := fun g h hgh => Subtype.ext (Subtype.ext (congrArg Subtype.val hgh :))
  haveI : Countable (Γ.subgroupOf N) := hj.countable
  haveI : DiscreteTopology (Γ.subgroupOf N) := DiscreteTopology.of_continuous_injective (f := j)
    (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) hj
  obtain ⟨C, hC, hs⟩ := hc
  refine GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one N (Γ.subgroupOf N) C hC fun g => ?_
  obtain ⟨γ, hγ, hk⟩ := hs g
  exact ⟨⟨γ, hγ⟩, hk⟩

theorem isMulRightInvariant_semi (N : Subgroup G) (s : K →* G) (hN : IsClosed (N : Set G)) (hs : Continuous s)
    (hc : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) (μ : Measure K) (ν : Measure N) [SFinite μ] [SFinite ν]
    [μ.IsMulRightInvariant] [ν.IsMulRightInvariant] : ((μ.prod ν).map (semiMap N s)).IsMulRightInvariant := by
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  have hcont : Continuous (semiMap N s) :=
    Continuous.subtype_mk ((continuous_subtype_val.comp continuous_snd).mul (hs.comp continuous_fst)) _
  refine ⟨fun x => ?_⟩
  obtain ⟨n₀, hn₀, h₀, hx⟩ := mem_sup_decomp N s hc x.2
  let T : K × N → K × N := fun p => (p.1 * h₀, p.2 * ⟨_, hc n₀ hn₀ p.1⟩)
  have hg : Continuous fun p : K × N => p.2 * (⟨_, hc n₀ hn₀ p.1⟩ : N) :=
    continuous_snd.mul (Continuous.subtype_mk (((hs.comp continuous_fst).mul continuous_const).mul
      (hs.comp continuous_fst).inv) _)
  have hT : MeasurePreserving T (μ.prod ν) (μ.prod ν) :=
    (measurePreserving_mul_right μ h₀).skew_product (g := fun h (n : N) => n * (⟨_, hc n₀ hn₀ h⟩ : N)) hg.measurable
      (Filter.Eventually.of_forall fun h => map_mul_right_eq_self ν _)
  have e : (· * x) ∘ semiMap N s = semiMap N s ∘ T := by
    funext p
    apply Subtype.ext
    simp only [Function.comp_apply, semiMap, T, Subgroup.coe_mul, hx, map_mul]
    group
  rw [Measure.map_map (measurable_mul_const x) hcont.measurable, e, ← Measure.map_map hcont.measurable hT.measurable,
    hT.map_eq]

theorem eq_of_rightInvariant {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ] (ν m : Measure G) (𝓝 𝓕 : Set G)
    (h1 : ν.IsHaarMeasure) (h2 : IsFundamentalDomain Γ 𝓝 ν) (h3 : ν 𝓝 = 1) (k0 : SigmaFinite m) (k1 : m.IsMulRightInvariant)
    (k2 : IsFundamentalDomain Γ 𝓕 m) (k3 : m 𝓕 = 1) : m = ν := by
  haveI : ν.IsMulRightInvariant := GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain Γ ν h2
    (by rw [h3]; exact one_ne_zero) (by rw [h3]; exact ENNReal.one_ne_top)
  have hinv : ν.inv 𝓝⁻¹ = 1 := by rw [Measure.inv_apply, inv_inv, h3]
  have e1 := measure_eq_div_smul m.inv ν.inv (s := 𝓝⁻¹) (by rw [hinv]; exact one_ne_zero) (by rw [hinv]; exact ENNReal.one_ne_top)
  rw [hinv, div_one, Measure.inv_apply, inv_inv] at e1
  set κ := m 𝓝 with hκ
  have e2 : m = κ • ν := by
    ext s -
    have := congrArg (fun μ : Measure G => μ s⁻¹) e1
    simpa only [Measure.inv_apply, inv_inv, Measure.smul_apply] using this
  haveI : m.IsMulLeftInvariant := by rw [e2]; infer_instance
  have h2' : IsFundamentalDomain Γ 𝓝 m := h2.mono (by rw [e2]; exact Measure.smul_absolutelyContinuous)
  have h4 : m 𝓝 = 1 := (h2'.measure_eq k2).trans k3
  have hk1 : κ = 1 := by rw [hκ]; exact h4
  rw [e2, hk1, one_smul]

end GlobalTheory.SemiMean

end
