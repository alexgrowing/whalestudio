import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft

open MeasureTheory

namespace GlobalTheory

theorem haar_inv_eq_of_lattice : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N]
    [T2Space N] [MeasurableSpace N] [BorelSpace N] (Λ : Subgroup N) [Countable Λ] (ν : MeasureTheory.Measure N) [ν.IsHaarMeasure]
    (𝓕 : Set N), MeasureTheory.IsFundamentalDomain Λ 𝓕 ν → ν 𝓕 ≠ 0 → ν 𝓕 ≠ ⊤ →
    MeasureTheory.Measure.map (fun n : N => n⁻¹) ν = ν := by
  intro N _ _ _ _ _ _ _ _ Λ _ ν _ 𝓕 h𝓕 h0 htop
  have hright : ∀ g : N, Measure.map (· * g) ν = ν := by
    intro g
    haveI : (Measure.map (· * g) ν).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right ν g
    set c := Measure.haarScalarFactor (Measure.map (· * g) ν) ν with hcdef
    have hc : Measure.map (· * g) ν = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
    have hqmp : Measure.QuasiMeasurePreserving (· * g) ν ν :=
      ⟨measurable_mul_const g, by rw [hc]; exact Measure.smul_absolutelyContinuous⟩
    have hfd : IsFundamentalDomain Λ ((· * g) ⁻¹' 𝓕) ν :=
      h𝓕.preimage_of_equiv hqmp (e := id) Function.bijective_id
        (fun l x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
    have h1 : ν ((· * g) ⁻¹' 𝓕) = ν 𝓕 := hfd.measure_eq h𝓕
    have h2 : ν ((· * g) ⁻¹' 𝓕) = (c : ENNReal) * ν 𝓕 := by
      have := (Homeomorph.mulRight g).toMeasurableEquiv.map_apply (μ := ν) 𝓕
      simp only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.coe_mulRight] at this
      rw [← this, hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    have h3 : (c : ENNReal) = 1 := by
      have : (c : ENNReal) * ν 𝓕 = 1 * ν 𝓕 := by rw [← h2, h1, one_mul]
      exact (ENNReal.mul_left_inj h0 htop).1 this
    have h4 : c = 1 := by exact_mod_cast h3
    rw [hc, h4, one_smul]
  haveI : ν.IsMulRightInvariant := ⟨hright⟩
  haveI := GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant ν
  exact Measure.IsInvInvariant.inv_eq_self

end GlobalTheory
