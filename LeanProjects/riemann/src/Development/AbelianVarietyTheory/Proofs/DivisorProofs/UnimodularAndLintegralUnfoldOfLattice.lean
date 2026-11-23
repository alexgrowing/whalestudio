import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine.RightUnfold

theorem isMulRightInvariant_of_lattice {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Λ : Subgroup G)
    [Countable Λ] (𝓑 : Set G) (h𝓑 : IsFundamentalDomain Λ 𝓑 ν) (hfin : ν 𝓑 ≠ ⊤) :
    ν.IsMulRightInvariant := by
  refine ⟨fun x => ?_⟩
  haveI : (ν.map (· * x)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right ν x
  have hc := Measure.isMulLeftInvariant_eq_smul (ν.map (· * x)) ν
  set c := Measure.haarScalarFactor (ν.map (· * x)) ν
  have h𝓑' : IsFundamentalDomain Λ ((· * x) ⁻¹' 𝓑) ν := by
    refine h𝓑.preimage_of_equiv (quasiMeasurePreserving_mul_right ν x) (e := id)
      Function.bijective_id ?_
    intro g y
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : ν ((· * x) ⁻¹' 𝓑) = ν 𝓑 := h𝓑'.measure_eq h𝓑
  have h0 : ν 𝓑 ≠ 0 := h𝓑.measure_ne_zero (NeZero.ne ν)
  have hmap : (ν.map (· * x)) 𝓑 = ν ((· * x) ⁻¹' 𝓑) :=
    MeasurableEquiv.map_apply (MeasurableEquiv.mulRight x) 𝓑
  have h1 : (c : ENNReal) * ν 𝓑 = 1 * ν 𝓑 := by
    calc (c : ENNReal) * ν 𝓑 = (c • ν) 𝓑 := by simp [Measure.smul_apply]
      _ = (ν.map (· * x)) 𝓑 := by rw [hc]
      _ = 1 * ν 𝓑 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h1
    exact_mod_cast this
  rw [hc, hc1, one_smul]

theorem isInvInvariant_of_right {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ENNReal := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h1 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul, ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h1
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h3 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h2
  have h4 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h3
  rw [hc, h4, one_smul]

theorem unimodular_and_unfold : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) (Λ : Subgroup G) [Countable Λ] (𝓑 : Set G), ν.IsHaarMeasure → IsFundamentalDomain Λ 𝓑 ν → ν 𝓑 ≠ ⊤ → ν.IsMulRightInvariant ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂ν = ∫⁻ b in 𝓑, ∑' γ : Λ, f (b⁻¹ * γ) ∂ν := by
  intro G _ _ _ _ _ _ _ _ ν Λ _ 𝓑 hν h𝓑 hfin
  haveI hR := isMulRightInvariant_of_lattice ν Λ 𝓑 h𝓑 hfin
  haveI := isInvInvariant_of_right ν
  refine ⟨hR, fun f hf => ?_⟩
  rw [← lintegral_inv_eq_self f, h𝓑.lintegral_eq_tsum' (fun x => f x⁻¹), lintegral_tsum]
  · refine tsum_congr fun γ => ?_
    refine lintegral_congr fun b => ?_
    simp [Subgroup.smul_def]
  · intro γ
    exact (hf.comp (measurable_inv.mul_const _)).aemeasurable

end GlobalTheory.ResLine.RightUnfold
