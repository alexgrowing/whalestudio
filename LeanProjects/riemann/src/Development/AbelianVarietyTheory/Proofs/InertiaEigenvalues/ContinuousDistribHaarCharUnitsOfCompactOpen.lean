import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR MeasureTheory Filter Topology
open scoped Pointwise

namespace GlobalTheory

theorem continuous_distribHaarChar_units_of_compact_open (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (μ : Measure R) [μ.IsAddHaarMeasure] (S : Set R) (hSo : IsOpen S) (hSc : IsCompact S)
    (hSn : S.Nonempty) : Continuous (fun u : Rˣ => distribHaarChar R u) := by
  obtain ⟨V, hV, hVS⟩ := compact_open_separated_mul_left hSc hSo subset_rfl
  have h0 : μ S ≠ 0 := hSo.measure_ne_zero μ hSn
  have ht : μ S ≠ ⊤ := hSc.measure_lt_top.ne
  have hle : ∀ u : Rˣ, (u : R) ∈ V → distribHaarChar R u ≤ 1 := by
    intro u hu
    have h1 : μ (u • S) ≤ μ S := by
      refine measure_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hVS ⟨u, hu, x, hx, rfl⟩
    rw [← distribHaarChar_mul μ u S] at h1
    have h2 : ((distribHaarChar R u : NNReal) : ENNReal) * μ S ≤ 1 * μ S := by simpa using h1
    have h3 := (ENNReal.mul_le_mul_iff_left h0 ht).1 h2
    exact_mod_cast h3
  refine continuous_of_continuousAt_one (distribHaarChar R : Rˣ →* NNReal) ?_
  have e1 : ∀ᶠ u : Rˣ in 𝓝 1, (u : R) ∈ V :=
    Units.continuous_val.continuousAt.eventually (show V ∈ 𝓝 ((1 : Rˣ) : R) by simpa using hV)
  have e2 : ∀ᶠ u : Rˣ in 𝓝 1, ((u⁻¹ : Rˣ) : R) ∈ V :=
    Units.continuous_coe_inv.continuousAt.eventually
      (show V ∈ 𝓝 (((1 : Rˣ)⁻¹ : Rˣ) : R) by simpa using hV)
  have e3 : (fun _ : Rˣ => (1 : NNReal)) =ᶠ[𝓝 1] (distribHaarChar R : Rˣ →* NNReal) := by
    filter_upwards [e1, e2] with u h1 h2
    have a1 := hle u h1
    have a2 := hle u⁻¹ h2
    have a3 : distribHaarChar R u * distribHaarChar R u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    refine le_antisymm ?_ a1
    calc (1 : NNReal) = distribHaarChar R u * distribHaarChar R u⁻¹ := a3.symm
      _ ≤ distribHaarChar R u * 1 := by gcongr
      _ = _ := mul_one _
  exact continuousAt_const.congr e3

theorem exists_isHaarMeasure_units_div_module : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [IsOpenUnits R] [MeasurableSpace R] [BorelSpace R] [BorelSpace Rˣ] (μ : Measure R), μ.IsAddHaarMeasure → (∃ S : Set R, IsOpen S ∧ IsCompact S ∧ S.Nonempty) → ∃ μ' : Measure Rˣ, μ'.IsHaarMeasure ∧ ∀ (g δ : R → ℂ), (∀ u : Rˣ, δ u = ((distribHaarChar R u : ℝ) : ℂ)) → ∀ T : Set Rˣ, MeasurableSet T → ∫ u in T, g u ∂μ' = ∫ t in Units.val '' T, g t * (δ t)⁻¹ ∂μ := by
  intro R _ _ _ _ _ _ _ _ _ _ μ hμ ⟨S, hSo, hSc, hSn⟩
  have hc := continuous_distribHaarChar_units_of_compact_open R μ S hSo hSc hSn
  have hoe : IsOpenEmbedding (Units.val : Rˣ → R) := IsOpenUnits.isOpenEmbedding_unitsVal
  have hme : MeasurableEmbedding (Units.val : Rˣ → R) := hoe.measurableEmbedding
  set ν : Measure Rˣ := μ.comap Units.val with hν
  set f : Rˣ → NNReal := fun u => distribHaarChar R u⁻¹ with hf
  have hfc : Continuous f := hc.comp continuous_inv
  have hνa : ∀ s : Set Rˣ, ν s = μ (Units.val '' s) := fun s => hme.comap_apply μ s
  haveI : IsLocallyFiniteMeasure ν := by
    refine ⟨fun x => ?_⟩
    obtain ⟨s, hs, hs'⟩ := μ.finiteAt_nhds (x : R)
    refine ⟨Units.val ⁻¹' s, hoe.continuous.continuousAt.preimage_mem_nhds hs, ?_⟩
    rw [hνa]
    exact (measure_mono (Set.image_preimage_subset _ _)).trans_lt hs'
  haveI : ν.IsOpenPosMeasure := by
    refine ⟨fun U hU hn => ?_⟩
    rw [hνa]
    exact (hoe.isOpenMap U hU).measure_ne_zero μ (hn.image _)
  haveI := IsLocallyFiniteMeasure.withDensity_coe (μ := ν) hfc
  have hpos : (ν.withDensity fun x => (f x : ENNReal)).IsOpenPosMeasure := by
    refine (withDensity_absolutelyContinuous' (μ := ν)
      (hfc.measurable.coe_nnreal_ennreal.aemeasurable) ?_).isOpenPosMeasure
    exact Eventually.of_forall fun x => by
      simpa [hf] using (distribHaarChar_pos (A := R) (g := x)).ne'
  have hinv : (ν.withDensity fun x => (f x : ENNReal)).IsMulLeftInvariant := by
    refine ⟨fun a => ?_⟩
    have hma : MeasurableEmbedding (fun x : Rˣ => a * x) :=
      (Homeomorph.mulLeft a).measurableEmbedding
    have hmap : Measure.map (fun x : Rˣ => a * x) ν = (f a : ENNReal) • ν := by
      ext s hs
      rw [hma.map_apply, Measure.smul_apply, hνa, hνa, smul_eq_mul, hf,
        distribHaarChar_mul μ a⁻¹]
      congr 1
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨_, ⟨a * x, hx, rfl⟩, by simp [Units.smul_def]⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨a⁻¹ * x, by simpa using hx, by simp [Units.smul_def]⟩
    ext s hs
    rw [hma.map_apply, withDensity_apply _ (hma.measurable hs), withDensity_apply _ hs]
    have h1 : ∀ x : Rˣ, (f x : ENNReal) = (f a⁻¹ : ENNReal) * (f (a * x) : ENNReal) := by
      intro x
      rw [← ENNReal.coe_mul, hf]
      simp only
      rw [← map_mul]
      congr 2
      simp [mul_comm a x, mul_left_comm]
    have h2 : (f a⁻¹ : ENNReal) * (f a : ENNReal) = 1 := by
      rw [← ENNReal.coe_mul, hf]
      simp only
      rw [← map_mul]
      simp
    calc ∫⁻ x in (fun x : Rˣ => a * x) ⁻¹' s, (f x : ENNReal) ∂ν
        = ∫⁻ x in (fun x : Rˣ => a * x) ⁻¹' s, (f a⁻¹ : ENNReal) * (f (a * x) : ENNReal) ∂ν := by
          exact lintegral_congr h1
      _ = (f a⁻¹ : ENNReal) * ∫⁻ x in (fun x : Rˣ => a * x) ⁻¹' s, (f (a * x) : ENNReal) ∂ν :=
          lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ = (f a⁻¹ : ENNReal) * ∫⁻ x in s, (f x : ENNReal) ∂(Measure.map (fun x : Rˣ => a * x) ν) := by
          rw [hma.restrict_map, hma.lintegral_map]
      _ = _ := by
          rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, h2,
            one_mul]
  refine ⟨ν.withDensity fun x => (f x : ENNReal), ⟨⟩, fun g δ hδ T hT => ?_⟩
  rw [setIntegral_withDensity_eq_setIntegral_smul hfc.measurable _ hT]
  have h3 := hme.setIntegral_map (μ := ν) (fun t => g t * (δ t)⁻¹) (Units.val '' T)
  rw [hν, hme.map_comap, Measure.restrict_restrict (hme.measurableSet_image.2 hT),
    Set.inter_eq_left.2 (Set.image_subset_range _ _),
    Set.preimage_image_eq _ hme.injective] at h3
  rw [h3]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [hδ, hf, map_inv, NNReal.smul_def, NNReal.coe_inv, Complex.real_smul]
  push_cast
  ring

end GlobalTheory
