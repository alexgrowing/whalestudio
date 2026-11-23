import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
open MeasureTheory

namespace GlobalTheory.HaarFundDom

open scoped Pointwise

theorem exists_haar_fundDom_mass_one : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ] (K : Set G), IsCompact K →
    (∀ g : G, ∃ γ : Γ, γ • g ∈ K) →
    ∃ (μ : Measure G) (𝓕 : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro G _ _ _ _ _ _ _ _ Γ _ _ K hK hcov
  let μ₀ : Measure G := Measure.haar
  obtain ⟨𝓕, h𝓕m, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  have hD : IsFundamentalDomain Γ 𝓕 μ₀ := IsFundamentalDomain.mk' h𝓕m.nullMeasurableSet h𝓕
  haveI : MeasurableMul G :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI : MeasurableConstSMul Γ G :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : G => (γ : G) * x).measurable⟩
  haveI : SMulInvariantMeasure Γ G μ₀ := ⟨fun γ A _ => measure_preimage_mul μ₀ (γ : G) A⟩
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hsub : 𝓕 ⊆ ⋃ γ : Γ, γ • K ∩ 𝓕 := by
    intro x hx
    obtain ⟨γ, hγ⟩ := hcov x
    refine Set.mem_iUnion.2 ⟨γ⁻¹, Set.mem_smul_set.2 ⟨γ • x, hγ, ?_⟩, hx⟩
    simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hfin : μ₀ 𝓕 < ⊤ :=
    calc μ₀ 𝓕 ≤ μ₀ (⋃ γ : Γ, γ • K ∩ 𝓕) := measure_mono hsub
      _ ≤ ∑' γ : Γ, μ₀ (γ • K ∩ 𝓕) := measure_iUnion_le _
      _ = μ₀ K := (hD.measure_eq_tsum _).symm
      _ < ⊤ := hK.measure_lt_top
  have hne : μ₀ 𝓕 ≠ 0 := by
    intro h0
    have h1 := hD.measure_eq_tsum' Set.univ
    simp only [Set.univ_inter, measure_smul, h0, tsum_zero] at h1
    exact (Measure.measure_univ_pos.2 (NeZero.ne μ₀)).ne' h1
  refine ⟨(μ₀ 𝓕)⁻¹ • μ₀, 𝓕, ?_, hD.mono Measure.smul_absolutelyContinuous, ?_⟩
  · exact Measure.IsHaarMeasure.smul μ₀ (ENNReal.inv_ne_zero.2 hfin.ne) (ENNReal.inv_ne_top.2 hne)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hne hfin.ne]

end GlobalTheory.HaarFundDom
