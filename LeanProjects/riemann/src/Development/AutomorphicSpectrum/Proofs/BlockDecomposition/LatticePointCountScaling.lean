import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

namespace GlobalTheory.CompanionTheory.RiemannCore

theorem tile_sum_estimate {G ι : Type} [MeasurableSpace G] [Countable ι] (μ : Measure G)
    (tile : ι → Set G) (hm : ∀ i, MeasurableSet (tile i))
    (hd : Pairwise (Function.onFun Disjoint tile)) (hc : ⋃ i, tile i = Set.univ) (n : ℕ)
    (hn : ∀ i, μ (tile i) = n) (a : ι → ℝ) (ha : Summable a) (f g : G → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ i, ∀ y ∈ tile i, |a i - f y| ≤ g y) :
    |(n : ℝ) * ∑' i, a i - ∫ y, f y ∂μ| ≤ ∫ y, g y ∂μ := by
  have hsum : ∀ {u : G → ℝ}, Integrable u μ →
      HasSum (fun i => ∫ y in tile i, u y ∂μ) (∫ y, u y ∂μ) := by
    intro u hu
    have := hasSum_integral_iUnion (f := u) (μ := μ) hm hd (by rw [hc]; exact hu.integrableOn)
    rwa [hc, setIntegral_univ] at this
  have hfin : ∀ i, μ (tile i) ≠ ⊤ := fun i => by rw [hn]; exact ENNReal.natCast_ne_top n
  have hconst : ∀ i, ∫ y in tile i, (a i - f y) ∂μ = (n : ℝ) * a i - ∫ y in tile i, f y ∂μ := by
    intro i
    have hi : Integrable (fun _ : G => a i) (μ.restrict (tile i)) := integrableOn_const (hfin i)
    rw [integral_sub hi hf.integrableOn, setIntegral_const]
    simp [Measure.real, hn, smul_eq_mul]
  have hA : HasSum (fun i => ∫ y in tile i, (a i - f y) ∂μ)
      ((n : ℝ) * ∑' i, a i - ∫ y, f y ∂μ) := by
    simp_rw [hconst]
    exact (ha.hasSum.mul_left _).sub (hsum hf)
  have key := hA.norm_le_of_bounded (hsum hg) (fun i => by
    refine norm_integral_le_of_norm_le hg.integrableOn ?_
    exact ae_restrict_of_forall_mem (hm i) (fun y hy => by
      simpa [Real.norm_eq_abs] using h i y hy))
  simpa [Real.norm_eq_abs] using key

section
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

theorem exists_nhds_close (φ : G → ℝ) (hc : Continuous φ) (hs : HasCompactSupport φ)
    {δ : ℝ} (hδ : 0 < δ) : ∃ V ∈ 𝓝 (0 : G), ∀ a b, a - b ∈ V → |φ a - φ b| < δ := by
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  have huc : UniformContinuous φ := hs.uniformContinuous_of_continuous hc
  have hmem := huc (Metric.dist_mem_uniformity hδ)
  rw [uniformity_eq_comap_nhds_zero G] at hmem
  obtain ⟨V, hV, hsub⟩ := Filter.mem_comap.1 hmem
  refine ⟨V, hV, fun a b hab => ?_⟩
  have h1 : (b, a) ∈ (fun p : G × G => p.2 - p.1) ⁻¹' V := hab
  have h2 := hsub h1
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Real.dist_eq] at h2
  rwa [abs_sub_comm]

variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G]

def cell (D : Set G) (R : Finset G) : Set G := ⋃ r ∈ R, (fun y => -r + y) ⁻¹' D

def tile (D : Set G) (R : Finset G) (l : G) : Set G := (fun y => -l + y) ⁻¹' cell D R

theorem mem_tile {D : Set G} {R : Finset G} {l y : G} :
    y ∈ tile D R l ↔ ∃ r ∈ R, y - r - l ∈ D := by
  simp only [tile, cell, Set.mem_preimage, Set.mem_iUnion, exists_prop]
  refine exists_congr fun r => and_congr Iff.rfl ?_
  have : -r + (-l + y) = y - r - l := by abel
  rw [this]

theorem measurableSet_cell {D : Set G} (hD : MeasurableSet D) (R : Finset G) :
    MeasurableSet (cell D R) :=
  Finset.measurableSet_biUnion _ fun r _ => (measurable_const_add (-r)) hD

theorem measurableSet_tile {D : Set G} (hD : MeasurableSet D) (R : Finset G) (l : G) :
    MeasurableSet (tile D R l) :=
  (measurable_const_add (-l)) (measurableSet_cell hD R)

theorem measure_tile (μ : Measure G) [μ.IsAddHaarMeasure] {D : Set G} (hD : MeasurableSet D)
    (hD1 : μ D = 1) (R : Finset G) (Λ : AddSubgroup G)
    (ht : ∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) (l : G) :
    μ (tile D R l) = (R.card : ENNReal) := by
  rw [tile, measure_preimage_add, cell, measure_biUnion_finset]
  · simp [measure_preimage_add, hD1]
  · intro r hr r' hr' hne
    refine Set.disjoint_left.2 fun y hy hy' => hne ?_
    simp only [Set.mem_preimage] at hy hy'
    have e1 : y - r - 0 ∈ D := by
      have : -r + y = y - r - 0 := by abel
      rwa [← this]
    have e2 : y - r' - 0 ∈ D := by
      have : -r' + y = y - r' - 0 := by abel
      rwa [← this]
    have := (ht y).unique (y₁ := (r, 0)) (y₂ := (r', 0)) ⟨hr, Λ.zero_mem, e1⟩ ⟨hr', Λ.zero_mem, e2⟩
    exact congrArg Prod.fst this
  · exact fun r _ => (measurable_const_add (-r)) hD

theorem tile_disjoint {D : Set G} {R : Finset G} {Λ : AddSubgroup G}
    (ht : ∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) :
    Pairwise (Function.onFun Disjoint fun l : Λ => tile D R (l : G)) := by
  intro l l' hne
  refine Set.disjoint_left.2 fun y hy hy' => hne ?_
  obtain ⟨r, hr, h⟩ := mem_tile.1 hy
  obtain ⟨r', hr', h'⟩ := mem_tile.1 hy'
  have := (ht y).unique (y₁ := (r, (l : G))) (y₂ := (r', (l' : G))) ⟨hr, l.2, h⟩ ⟨hr', l'.2, h'⟩
  exact Subtype.ext (congrArg Prod.snd this)

theorem tile_cover {D : Set G} {R : Finset G} {Λ : AddSubgroup G}
    (ht : ∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) :
    ⋃ l : Λ, tile D R (l : G) = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨⟨r, l⟩, ⟨hr, hl, h⟩, -⟩ := ht y
  exact Set.mem_iUnion.2 ⟨⟨l, hl⟩, mem_tile.2 ⟨r, hr, h⟩⟩

theorem finite_lattice_points (μ : Measure G) [μ.IsAddHaarMeasure] {D K₀ : Set G}
    (hD : MeasurableSet D) (hK : IsCompact K₀) (hDK : D ⊆ K₀) (hD1 : μ D = 1) (R : Finset G)
    (Λ : AddSubgroup G) (ht : ∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D)
    (x0 : G) {C : Set G} (hC : IsCompact C) : {l : Λ | x0 + (l : G) ∈ C}.Finite := by
  have hR : 1 ≤ R.card := by
    obtain ⟨⟨r, l⟩, ⟨hr, -, -⟩, -⟩ := ht 0
    exact Finset.card_pos.2 ⟨r, hr⟩
  set Q : Set G := (fun p : G × G × G => p.1 - x0 + p.2.1 + p.2.2) '' (C ×ˢ ((R : Set G) ×ˢ K₀))
    with hQ
  have hQc : IsCompact Q :=
    (hC.prod (R.finite_toSet.isCompact.prod hK)).image (by fun_prop)
  let As : {l : Λ // x0 + (l : G) ∈ C} → Set G := fun l => tile D R ((l : Λ) : G)
  have hsub : ⋃ i, As i ⊆ Q := by
    refine Set.iUnion_subset fun l y hy => ?_
    obtain ⟨r, hr, h⟩ := mem_tile.1 hy
    refine ⟨(x0 + ((l : Λ) : G), r, y - r - ((l : Λ) : G)), ⟨l.2, hr, hDK h⟩, ?_⟩
    simp only
    abel
  have hfin := Measure.finite_const_le_meas_of_disjoint_iUnion μ (ε := 1) one_pos (As := As)
    (fun l => measurableSet_tile hD R _)
    (fun l l' hne => tile_disjoint ht (fun h => hne (Subtype.ext h)))
    (ne_top_of_le_ne_top hQc.measure_lt_top.ne (measure_mono hsub))
  have huniv : {i | (1 : ENNReal) ≤ μ (As i)} = Set.univ := by
    refine Set.eq_univ_of_forall fun l => ?_
    show 1 ≤ μ (tile D R _)
    rw [measure_tile μ hD hD1 R Λ ht]
    exact_mod_cast hR
  rw [huniv] at hfin
  exact Set.finite_coe_iff.1 (Set.finite_univ_iff.1 hfin)

theorem scaling (μ : Measure G) {τ : G → G} (hτ : MeasurableEmbedding τ) {c : ℝ} (hc : 0 ≤ c)
    (hmap : Measure.map τ μ = ENNReal.ofReal c • μ) {h : G → ℝ} (hh : Integrable h μ) :
    Integrable (fun y => h (τ y)) μ ∧ ∫ y, h (τ y) ∂μ = c * ∫ y, h y ∂μ := by
  constructor
  · have h1 : Integrable h (Measure.map τ μ) := by
      rw [hmap]; exact hh.smul_measure ENNReal.ofReal_ne_top
    exact hτ.integrable_map_iff.1 h1
  · rw [← hτ.integral_map, hmap, integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]

end

theorem main : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (Λ : AddSubgroup G) [Countable Λ] (D K₀ : Set G) (R : Finset G) (T : ℝ → G →+ G) (M : ℕ), MeasurableSet D → IsCompact K₀ → D ⊆ K₀ → μ D = 1 → (∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) → (∀ ε : ℝ, 0 < ε → Continuous (T ε)) → (∀ ε : ℝ, 0 < ε → ∀ y, T ε⁻¹ (T ε y) = y ∧ T ε (T ε⁻¹ y) = y) → (∀ ε : ℝ, 0 < ε → Measure.map (T ε) μ = ENNReal.ofReal ((ε ^ M)⁻¹) • μ) → (∀ B : Set G, IsCompact B → ∀ U ∈ 𝓝 (0 : G), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ b ∈ B, T ε b ∈ U) → ∀ (x0 : G) (φ : G → ℝ), Continuous φ → HasCompactSupport φ → (∀ ε : ℝ, 0 < ε → Summable fun l : Λ => φ (T ε (x0 + l))) ∧ Tendsto (fun ε : ℝ => ε ^ M * ∑' l : Λ, φ (T ε (x0 + l))) (𝓝[>] 0) (𝓝 ((R.card : ℝ)⁻¹ * ∫ y, φ y ∂μ)) := by
  intro G _ _ _ _ _ _ _ _ μ _ Λ _ D K₀ R T M hD hK hDK hD1 ht hcont hinv hscale hshrink x0 φ hφc hφs
  let τ : ∀ ε : ℝ, 0 < ε → G ≃ₜ G := fun ε hε =>
    { toFun := T ε
      invFun := T ε⁻¹
      left_inv := fun y => (hinv ε hε y).1
      right_inv := fun y => (hinv ε hε y).2
      continuous_toFun := hcont ε hε
      continuous_invFun := hcont ε⁻¹ (inv_pos.2 hε) }
  have hsummable : ∀ ε : ℝ, 0 < ε → Summable fun l : Λ => φ (T ε (x0 + l)) := by
    intro ε hε
    have hfin := finite_lattice_points μ hD hK hDK hD1 R Λ ht x0 (C := T ε⁻¹ '' tsupport φ)
      (IsCompact.image hφs (hcont _ (inv_pos.2 hε)))
    refine summable_of_finite_support (hfin.subset ?_)
    intro l hl
    exact ⟨T ε (x0 + l), subset_tsupport _ hl, (hinv ε hε _).1⟩
  refine ⟨hsummable, ?_⟩
  obtain ⟨W, hWc, hW⟩ := exists_compact_mem_nhds (0 : G)
  set C : Set G := (fun p : G × G => p.1 - p.2) '' (tsupport φ ×ˢ W) with hC
  have hCc : IsCompact C := (IsCompact.prod hφs hWc).image (by fun_prop)
  have hCm : MeasurableSet C := hCc.measurableSet
  set B : Set G := (fun p : G × G => x0 - p.1 - p.2) '' ((R : Set G) ×ˢ K₀) with hB
  have hBc : IsCompact B := (R.finite_toSet.isCompact.prod hK).image (by fun_prop)
  have hRpos : (0 : ℝ) < R.card := by
    obtain ⟨⟨r, l⟩, ⟨hr, -, -⟩, -⟩ := ht 0
    exact_mod_cast Finset.card_pos.2 ⟨r, hr⟩
  have hφi : Integrable φ μ := hφc.integrable_of_hasCompactSupport hφs
  have hCi : Integrable (C.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_indicator_iff hCm).2 (integrableOn_const hCc.measure_lt_top.ne)
  have hkey : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      |ε ^ M * ∑' l : Λ, φ (T ε (x0 + l)) - (R.card : ℝ)⁻¹ * ∫ y, φ y ∂μ| ≤
        δ * (μ.real C / R.card) := by
    intro δ hδ
    obtain ⟨V₁, hV₁, hclose⟩ := exists_nhds_close φ hφc hφs hδ
    filter_upwards [hshrink B hBc (V₁ ∩ W) (inter_mem hV₁ hW), self_mem_nhdsWithin]
      with ε hε hpos
    have hpos' : 0 < ε := hpos
    have hpow : 0 < ε ^ M := pow_pos hpos' M
    have hemb : MeasurableEmbedding (T ε) := (τ ε hpos').measurableEmbedding
    obtain ⟨hi1, he1⟩ := scaling μ hemb (inv_nonneg.2 hpow.le) (hscale ε hpos') hφi
    obtain ⟨hi2, he2⟩ := scaling μ hemb (inv_nonneg.2 hpow.le) (hscale ε hpos') hCi
    have est := tile_sum_estimate μ (fun l : Λ => tile D R (l : G))
      (fun l => measurableSet_tile hD R _) (tile_disjoint ht) (tile_cover ht) R.card
      (fun l => measure_tile μ hD hD1 R Λ ht _) (fun l : Λ => φ (T ε (x0 + l)))
      (hsummable ε hpos') (fun y => φ (T ε y))
      (fun y => δ * C.indicator (fun _ => (1 : ℝ)) (T ε y)) hi1 (hi2.const_mul δ) (by
        intro l y hy
        obtain ⟨r, hr, hyd⟩ := mem_tile.1 hy
        have hb : x0 + (l : G) - y ∈ B :=
          ⟨(r, y - r - l), ⟨hr, hDK hyd⟩, by simp only; abel⟩
        have hTU := hε _ hb
        rw [map_sub] at hTU
        generalize T ε (x0 + (l : G)) = a at hTU ⊢
        generalize T ε y = b at hTU ⊢
        by_cases hbC : b ∈ C
        · rw [Set.indicator_of_mem hbC]
          simpa using (hclose a b hTU.1).le
        · have hb0 : φ b = 0 := by
            by_contra h
            exact hbC ⟨(b, 0), ⟨subset_tsupport _ h, mem_of_mem_nhds hW⟩, by simp⟩
          have ha0 : φ a = 0 := by
            by_contra h
            exact hbC ⟨(a, a - b), ⟨subset_tsupport _ h, hTU.2⟩, by simp⟩
          rw [Set.indicator_of_notMem hbC]
          simp [ha0, hb0])
    rw [he1, integral_const_mul, he2, integral_indicator_const _ hCm] at est
    simp only [smul_eq_mul, mul_one] at est
    have hid : ε ^ M * ∑' l : Λ, φ (T ε (x0 + l)) - (R.card : ℝ)⁻¹ * ∫ y, φ y ∂μ =
        (ε ^ M / R.card) * ((R.card : ℝ) * ∑' l : Λ, φ (T ε (x0 + l)) -
          (ε ^ M)⁻¹ * ∫ y, φ y ∂μ) := by
      field_simp
    rw [hid, abs_mul, abs_of_pos (div_pos hpow hRpos)]
    calc ε ^ M / R.card * _ ≤ ε ^ M / R.card * (δ * ((ε ^ M)⁻¹ * μ.real C)) :=
          mul_le_mul_of_nonneg_left est (div_pos hpow hRpos).le
      _ = δ * (μ.real C / R.card) := by field_simp
  rw [Metric.tendsto_nhds]
  intro η hη
  have hK0 : 0 ≤ μ.real C / R.card := div_nonneg measureReal_nonneg hRpos.le
  set L := μ.real C / R.card with hL
  have hδ : 0 < η / (L + 1) := by positivity
  filter_upwards [hkey _ hδ] with ε hε
  rw [Real.dist_eq]
  refine lt_of_le_of_lt hε ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.CompanionTheory.RiemannCore
