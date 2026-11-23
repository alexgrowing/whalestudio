import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasConstTermConst
open MeasureTheory

noncomputable section

namespace GlobalTheory.ThK.RankRed.MeanConst

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem rightInv (Γ : Subgroup G) [Countable Γ] (ν : Measure G) [ν.IsHaarMeasure] {𝓝 : Set G}
    (h𝓝 : IsFundamentalDomain Γ 𝓝 ν) (hfin : ν 𝓝 ≠ ⊤) : ν.IsMulRightInvariant := ⟨fun n₀ => by
  let φ := Homeomorph.mulRight n₀
  haveI : (ν.map φ).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right ν n₀
  have hc := Measure.isMulLeftInvariant_eq_smul (ν.map φ) ν
  set c := Measure.haarScalarFactor (ν.map φ) ν
  have hq : Measure.QuasiMeasurePreserving φ ν ν :=
    ⟨φ.continuous.measurable, by rw [hc]; exact Measure.smul_absolutelyContinuous⟩
  have h𝓝' : IsFundamentalDomain Γ (φ ⁻¹' 𝓝) ν :=
    h𝓝.preimage_of_equiv hq (e := id) Function.bijective_id fun g x => mul_assoc _ _ _
  have hm : ν (φ ⁻¹' 𝓝) = ν 𝓝 := h𝓝'.measure_eq h𝓝
  have h0 : ν 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne ν)
  have hmap : (ν.map φ) 𝓝 = ν (φ ⁻¹' 𝓝) := MeasurableEquiv.map_apply φ.toMeasurableEquiv 𝓝
  have h1 : (c : ENNReal) * ν 𝓝 = 1 * ν 𝓝 := by
    calc (c : ENNReal) * ν 𝓝 = (c • ν) 𝓝 := by simp [Measure.smul_apply]
      _ = (ν.map φ) 𝓝 := by rw [hc]
      _ = 1 * ν 𝓝 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h1
    exact_mod_cast this
  show ν.map φ = ν
  rw [hc, hc1, one_smul]⟩

theorem setIntegral_mul_right (Γ : Subgroup G) [Countable Γ] (ν : Measure G)
    [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] {fd : Set G} (hfd : IsFundamentalDomain Γ fd ν) {φ : G → ℂ}
    (hφ : ∀ γ ∈ Γ, ∀ u, φ (γ * u) = φ u) (k : G) :
    ∫ u in fd, φ (u * k) ∂ν = ∫ u in fd, φ u ∂ν := by
  have hmp : MeasurePreserving (· * k) ν ν := measurePreserving_mul_right ν k
  have hme : MeasurableEmbedding (· * k) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd' : IsFundamentalDomain Γ ((· * k⁻¹) ⁻¹' fd) ν := by
    refine hfd.preimage_of_equiv (measurePreserving_mul_right ν k⁻¹).quasiMeasurePreserving (e := id)
      Function.bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ g : Γ, ∀ x, φ (g • x) = φ x := fun g x => hφ g g.2 x
  have hpre : (· * k) ⁻¹' ((· * k⁻¹) ⁻¹' fd) = fd := by
    ext u; simp
  have h3 := hmp.setIntegral_preimage_emb hme φ ((· * k⁻¹) ⁻¹' fd)
  rw [hpre] at h3
  rw [h3]
  exact hfd'.setIntegral_eq hfd hinv

end GlobalTheory.ThK.RankRed.MeanConst
