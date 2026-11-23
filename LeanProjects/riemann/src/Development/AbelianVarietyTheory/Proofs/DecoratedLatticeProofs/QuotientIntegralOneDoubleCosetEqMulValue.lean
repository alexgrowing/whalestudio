import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
open MeasureTheory GlobalTheory.Grow

namespace GlobalTheory

theorem quotientIntegral_oneDoubleCoset_eq_mul_value (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (R K : Subgroup G)
    (hR : IsClosed (R : Set G)) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (ρ : Measure R) (μ : Measure G) (hρ : ρ.IsHaarMeasure) (hρr : ρ.IsMulRightInvariant) (hμ : μ.IsHaarMeasure)
    (t : G) : ∃ w : ℂ, w ≠ 0 ∧ ∀ f : G → ℂ, (∀ r ∈ R, ∀ g, f (r * g) = f g) → (∀ k ∈ K, ∀ g, f (g * k) = f g) →
      (∀ g, f g ≠ 0 → ∃ r ∈ R, ∃ k ∈ K, g = r * t * k) → IsQuotIntL1 ρ μ f (w * f t) := by

  set T : Set G := {g | t⁻¹ * g ∈ K} with hT
  set S : Set R := {r | t⁻¹ * ((r : G) * t) ∈ K} with hS
  have hemb : Topology.IsClosedEmbedding (Subtype.val : R → G) := hR.isClosedEmbedding_subtypeVal

  have hAo : ∀ h : G, IsOpen {r : R | t⁻¹ * ((r : G) * h) ∈ K} := fun h =>
    hKo.preimage (continuous_const.mul (continuous_subtype_val.mul continuous_const))
  have hAc : ∀ h : G, IsCompact {r : R | t⁻¹ * ((r : G) * h) ∈ K} := fun h => by
    have h1 : IsCompact ((fun g : G => t⁻¹ * (g * h)) ⁻¹' (K : Set G)) := by
      have e : (fun g : G => t⁻¹ * (g * h)) ⁻¹' (K : Set G) = (fun g => t * g * h⁻¹) '' (K : Set G) := by
        ext g; constructor
        · intro hg; exact ⟨t⁻¹ * (g * h), hg, by group⟩
        · rintro ⟨k, hk, rfl⟩; simpa [mul_assoc] using hk
      rw [e]; exact hKc.image (by fun_prop)
    exact hemb.isCompact_preimage h1
  have hTm : MeasurableSet T := (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμT : μ T = μ K := measure_preimage_mul μ t⁻¹ K
  have hμK0 : μ K ≠ 0 := (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hμKt : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hSo : IsOpen S := by simpa using hAo t
  have hSc : IsCompact S := by simpa using hAc t
  have hρS0 : ρ S ≠ 0 := (hSo.measure_pos ρ ⟨1, by simp [hS]⟩).ne'
  have hρSt : ρ S ≠ ⊤ := hSc.measure_lt_top.ne
  set c : ℝ := ρ.real S with hc
  have hc0 : c ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hρS0, hρSt⟩
  have hμK : μ.real K ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hμK0, hμKt⟩
  refine ⟨(μ.real K : ℂ) / (c : ℂ), div_ne_zero (by exact_mod_cast hμK) (by exact_mod_cast hc0), fun f hfl hfr hfs => ?_⟩
  set a : ℂ := f t / (c : ℂ) with ha
  refine ⟨T.indicator fun _ => a, ?_, fun h => ?_, fun h => ?_, ?_⟩
  · exact (integrable_indicator_iff hTm).2 (integrableOn_const (by rw [hμT]; exact hμKt))
  · have e : (fun r : R => T.indicator (fun _ => a) ((r : G) * h)) =
        {r : R | t⁻¹ * ((r : G) * h) ∈ K}.indicator fun _ => a := by
      rfl
    rw [e]
    exact (integrable_indicator_iff (hAo h).measurableSet).2
      (integrableOn_const (hAc h).measure_lt_top.ne)
  · have e : (fun r : R => T.indicator (fun _ => a) ((r : G) * h)) =
        {r : R | t⁻¹ * ((r : G) * h) ∈ K}.indicator fun _ => a := by
      rfl
    rw [e, integral_indicator_const _ (hAo h).measurableSet]
    by_cases hne : ∃ s ∈ R, ∃ k ∈ K, h = s * t * k
    · obtain ⟨s, hs, k, hk, rfl⟩ := hne
      have eA : {r : R | t⁻¹ * ((r : G) * (s * t * k)) ∈ K} = (fun r : R => r * ⟨s, hs⟩) ⁻¹' S := by
        ext r
        simp only [hS, Set.mem_preimage, Set.mem_ofPred_eq, Subgroup.coe_mul]
        have : t⁻¹ * ((r : G) * (s * t * k)) = t⁻¹ * ((r : G) * s * t) * k := by group
        rw [this, Subgroup.mul_mem_cancel_right _ hk]
      have e1 : ρ.real {r : R | t⁻¹ * ((r : G) * (s * t * k)) ∈ K} = c := by
        rw [eA, hc, measureReal_def, measureReal_def, measure_preimage_mul_right]
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
      rw [e1, ha, mul_assoc, hfl s hs, hfr k hk, Complex.real_smul]
      field_simp
    · have hf : f h = 0 := by
        by_contra hf; exact hne (hfs h hf)
      have eA : {r : R | t⁻¹ * ((r : G) * h) ∈ K} = ∅ := by
        ext r
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hr
        exact hne ⟨(r : G)⁻¹, inv_mem r.2, t⁻¹ * ((r : G) * h), hr, by group⟩
      rw [hf, eA]; simp
  · rw [integral_indicator_const _ hTm]
    have e2 : μ.real T = μ.real K := by simp only [measureReal_def, hμT]
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
    rw [e2, ha, Complex.real_smul]
    field_simp

end GlobalTheory
