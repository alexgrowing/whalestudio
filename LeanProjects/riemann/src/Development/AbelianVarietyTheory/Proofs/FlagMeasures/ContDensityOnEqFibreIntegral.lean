import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal

namespace GlobalTheory.FibreDensity

theorem not_pos_of_setIntegral_isCompact_eq_zero {X : Type} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {B : Set X} (hB : IsOpen B) {h : X → ℝ}
    (hh : ContinuousOn h B) (h0 : ∀ S : Set X, IsCompact S → S ⊆ B → ∫ x in S, h x ∂ν = 0)
    {b : X} (hb : b ∈ B) : ¬ 0 < h b := by
  intro hpos
  have hev : ∀ᶠ x in nhds b, h b / 2 < h x := by
    have h1 : ∀ᶠ x in nhdsWithin b B, h b / 2 < h x :=
      (hh b hb).eventually (lt_mem_nhds (by linarith))
    rwa [hB.nhdsWithin_eq hb] at h1
  obtain ⟨U, hUsub, hUo, hbU⟩ := mem_nhds_iff.1 (Filter.inter_mem (hB.mem_nhds hb) hev)
  obtain ⟨K, hK, hbK, hKU⟩ := exists_compact_subset hUo hbU
  have hKB : K ⊆ B := fun x hx => (hUsub (hKU hx)).1
  have hKh : ∀ x ∈ K, h b / 2 < h x := fun x hx => (hUsub (hKU hx)).2
  have hle : ∫ _ in K, h b / 2 ∂ν ≤ ∫ x in K, h x ∂ν :=
    setIntegral_mono_on (continuousOn_const.integrableOn_compact hK)
      ((hh.mono hKB).integrableOn_compact hK) hK.measurableSet (fun x hx => (hKh x hx).le)
  rw [setIntegral_const, h0 K hK hKB, smul_eq_mul] at hle
  have hKpos : 0 < ν K :=
    lt_of_lt_of_le (isOpen_interior.measure_pos ν ⟨b, hbK⟩) (measure_mono interior_subset)
  have hreal : 0 < ν.real K := ENNReal.toReal_pos hKpos.ne' hK.measure_lt_top.ne
  have := mul_pos hreal (half_pos hpos)
  linarith

theorem eq_zero_of_setIntegral_isCompact_eq_zero {X : Type} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {B : Set X} (hB : IsOpen B) {h : X → ℝ}
    (hh : ContinuousOn h B) (h0 : ∀ S : Set X, IsCompact S → S ⊆ B → ∫ x in S, h x ∂ν = 0)
    {b : X} (hb : b ∈ B) : h b = 0 := by
  have h1 := not_pos_of_setIntegral_isCompact_eq_zero ν hB hh h0 hb
  have h2 : ¬ 0 < -h b := not_pos_of_setIntegral_isCompact_eq_zero ν hB (h := fun x => -h x) hh.neg
    (fun S hS hSB => by rw [integral_neg, h0 S hS hSB, neg_zero]) hb
  linarith [not_lt.1 h1, not_lt.1 h2]

theorem eq_of_setIntegral_isCompact_eq {X : Type} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {B : Set X} (hB : IsOpen B) {g h : X → ℂ}
    (hg : ContinuousOn g B) (hh : ContinuousOn h B)
    (h0 : ∀ S : Set X, IsCompact S → S ⊆ B → ∫ x in S, g x ∂ν = ∫ x in S, h x ∂ν)
    {b : X} (hb : b ∈ B) : g b = h b := by
  have hk : ContinuousOn (fun x => g x - h x) B := hg.sub hh
  have hint : ∀ S : Set X, IsCompact S → S ⊆ B → ∫ x in S, (g x - h x) ∂ν = 0 := by
    intro S hS hSB
    rw [integral_sub ((hg.mono hSB).integrableOn_compact hS) ((hh.mono hSB).integrableOn_compact hS),
      h0 S hS hSB, sub_self]
  have hre : (g b - h b).re = 0 :=
    eq_zero_of_setIntegral_isCompact_eq_zero ν hB (h := fun x => (g x - h x).re)
      (Complex.continuous_re.comp_continuousOn hk) (fun S hS hSB => by
        have e := Complex.reCLM.integral_comp_comm ((hk.mono hSB).integrableOn_compact (μ := ν) hS).integrable
        simp only [Complex.reCLM_apply] at e
        rw [e, hint S hS hSB, Complex.zero_re]) hb
  have him : (g b - h b).im = 0 :=
    eq_zero_of_setIntegral_isCompact_eq_zero ν hB (h := fun x => (g x - h x).im)
      (Complex.continuous_im.comp_continuousOn hk) (fun S hS hSB => by
        have e := Complex.imCLM.integral_comp_comm ((hk.mono hSB).integrableOn_compact (μ := ν) hS).integrable
        simp only [Complex.imCLM_apply] at e
        rw [e, hint S hS hSB, Complex.zero_im]) hb
  have hz : g b - h b = 0 := Complex.ext (by simpa using hre) (by simpa using him)
  exact sub_eq_zero.1 hz

theorem contDensityOn_eq_fibre_integral : ∀ (V X : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (f : V → X) (ν : Measure X) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] (B : Set X) (fib : X → Measure V) (φ : V → ℝ) (g : X → ℂ), Continuous f → IsOpen B → IsFibreFamily μ f id Set.univ ν B fib → Continuous φ → HasCompactSupport φ → (∀ v, 0 ≤ φ v) → IsContDensityOn μ f id ν B (fun v => (φ v : ℂ)) g → ∀ b ∈ B, g b = ((∫ v, φ v ∂(fib b) : ℝ) : ℂ) ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) = ENNReal.ofReal (g b).re := by
  intro V X _ _ _ _ _ _ _ _ μ f ν _ _ B fib φ g hf hB hfib hφ hφc hφ0 hdens
  obtain ⟨hconc, hdis, hreg⟩ := hfib
  obtain ⟨hgc, hgint⟩ := hdens
  have hφm : Measurable φ := hφ.measurable
  obtain ⟨hφi, hGc⟩ := hreg φ hφ hφc (Set.subset_univ _)
  set G : X → ℝ := fun b => ∫ v, φ v ∂(fib b) with hG
  have hG0 : ∀ b, 0 ≤ G b := fun b => integral_nonneg (fun v => hφ0 v)
  have hlin : ∀ b ∈ B, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) = ENNReal.ofReal (G b) := fun b hb =>
    (ofReal_integral_eq_lintegral_ofReal (hφi b hb) (Filter.Eventually.of_forall hφ0)).symm
  have key : ∀ S : Set X, IsCompact S → S ⊆ B →
      ∫ x in S, g x ∂ν = ∫ x in S, ((G x : ℝ) : ℂ) ∂ν := by
    intro S hS hSB
    have hSm : MeasurableSet S := hS.measurableSet
    have hpre : MeasurableSet (f ⁻¹' S) := hf.measurable hSm

    have hL : ∫⁻ v in f ⁻¹' S, ENNReal.ofReal (φ v) ∂μ = ∫⁻ b in S, ENNReal.ofReal (G b) ∂ν := by
      have h2 := hdis ((f ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ v)))
        ((ENNReal.measurable_ofReal.comp hφm).indicator hpre)
      rw [Measure.restrict_univ, lintegral_indicator hpre] at h2
      rw [h2, ← lintegral_indicator hSm]
      apply lintegral_congr
      intro b
      have hae : ∀ᵐ v ∂(fib b), f v = b := by
        rw [ae_iff]
        refine measure_mono_null ?_ (hconc b)
        intro v hv
        simpa using hv
      by_cases hbS : b ∈ S
      · rw [Set.indicator_of_mem hbS, ← hlin b (hSB hbS)]
        apply lintegral_congr_ae
        filter_upwards [hae] with v hv
        simp [hv, hbS]
      · calc ∫⁻ v, (f ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ v)) v ∂(fib b)
            = ∫⁻ _, 0 ∂(fib b) := by
              apply lintegral_congr_ae
              filter_upwards [hae] with v hv
              simp [hv, hbS]
          _ = S.indicator (fun b => ENNReal.ofReal (G b)) b := by
              simp [hbS]
    have hGS : IntegrableOn G S ν := (hGc.mono hSB).integrableOn_compact hS
    have hφS : ∫ v in f ⁻¹' S, φ v ∂μ = ∫ b in S, G b ∂ν := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hφ0)
          hφ.aestronglyMeasurable,
        integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hG0)
          hGS.integrable.aestronglyMeasurable, hL]
    have e := hgint S hS hSB
    simp only [Set.image_id] at e
    rw [← e, integral_complex_ofReal, integral_complex_ofReal, hφS]
  intro b hb
  have hgb : g b = ((G b : ℝ) : ℂ) :=
    eq_of_setIntegral_isCompact_eq ν hB hgc (Complex.continuous_ofReal.comp_continuousOn hGc) key hb
  refine ⟨hgb, ?_⟩
  rw [hlin b hb, hgb, Complex.ofReal_re]

end GlobalTheory.FibreDensity
