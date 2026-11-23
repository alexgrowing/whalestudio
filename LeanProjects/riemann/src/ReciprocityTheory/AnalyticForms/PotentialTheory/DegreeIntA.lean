import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def DIChartDens (A : FinHolAtlas e X) (D : Fin A.n → (Fin e → ℂ) → ℝ) : Prop :=
  ∀ a b, ∀ z ∈ (A.chart a).target, (A.chart a).symm z ∈ (A.chart b).source →
    D a z = D b (A.chart b ((A.chart a).symm z)) *
      ‖LinearMap.det (fderiv ℂ (A.chart b ∘ (A.chart a).symm) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2

theorem dI_chartDens_locDens (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) : DIChartDens A (locDens A Φ) :=
  fun a b z hz hz2 => locDensChart A Φ hΦ a b z hz hz2

theorem dI_chartDens_abs (A : FinHolAtlas e X) {D : Fin A.n → (Fin e → ℂ) → ℝ}
    (hD : DIChartDens A D) : DIChartDens A (fun a z => |D a z|) := by
  intro a b z hz hzb
  beta_reduce
  rw [hD a b z hz hzb, abs_mul, abs_pow, abs_norm]

theorem dI_transfer (A : FinHolAtlas e X) {D : Fin A.n → (Fin e → ℂ) → ℝ} (hD : DIChartDens A D)
    (a b : Fin A.n) (f : X → ℝ) (hf : ∀ x, x ∉ (A.chart a).source → f x = 0)
    (hint : IntegrableOn (fun y => f ((A.chart a).symm y) * D a y) (A.chart a).target) :
    IntegrableOn (fun y => f ((A.chart b).symm y) * D b y) (A.chart b).target ∧
    ∫ y in (A.chart b).target, f ((A.chart b).symm y) * D b y =
      ∫ y in (A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source,
        f ((A.chart a).symm y) * D a y := by
  have hU : IsOpen ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source) :=
    (A.chart a).continuousOn_symm.isOpen_inter_preimage (A.chart a).open_target
      (A.chart b).open_source
  have hτ : AnalyticOnNhd ℂ (A.chart b ∘ (A.chart a).symm)
      ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source) := A.holo a b
  have hinj : Set.InjOn (A.chart b ∘ (A.chart a).symm)
      ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source) := by
    intro u hu v hv huv
    exact (A.chart a).symm.injOn hu.1 hv.1 ((A.chart b).injOn hu.2 hv.2 huv)
  have himg : (A.chart b ∘ (A.chart a).symm) ''
      ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source) ⊆ (A.chart b).target := by
    rintro _ ⟨z, hz, rfl⟩; exact (A.chart b).map_source hz.2
  have hin : ∀ w ∈ (A.chart b).target, (A.chart b).symm w ∈ (A.chart a).source →
      w ∈ (A.chart b ∘ (A.chart a).symm) ''
        ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source) := by
    intro w hw h2
    refine ⟨A.chart a ((A.chart b).symm w), ⟨(A.chart a).map_source h2, ?_⟩, ?_⟩
    · show (A.chart a).symm (A.chart a ((A.chart b).symm w)) ∈ (A.chart b).source
      rw [(A.chart a).left_inv h2]; exact (A.chart b).map_target hw
    · show A.chart b ((A.chart a).symm (A.chart a ((A.chart b).symm w))) = w
      rw [(A.chart a).left_inv h2, (A.chart b).right_inv hw]
  have hzero : ∀ w ∈ (A.chart b).target \ (A.chart b ∘ (A.chart a).symm) ''
      ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source),
      f ((A.chart b).symm w) * D b w = 0 := by
    rintro w ⟨hw, hwU⟩
    have h1 : (A.chart b).symm w ∉ (A.chart a).source := fun h => hwU (hin w hw h)
    simp [hf _ h1]
  have heq : ∀ z ∈ (A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source,
      Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart b ∘ (A.chart a).symm) z).det *
        (f ((A.chart b).symm ((A.chart b ∘ (A.chart a).symm) z)) *
          D b ((A.chart b ∘ (A.chart a).symm) z)) = f ((A.chart a).symm z) * D a z := by
    intro z hz
    have hz2 : (A.chart a).symm z ∈ (A.chart b).source := hz.2
    simp only [Function.comp_apply, (A.chart b).left_inv hz2]
    rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, hD a b z hz.1 hz2]
    ring
  have hIU : IntegrableOn (fun y => f ((A.chart a).symm y) * D a y)
      ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source) :=
    hint.mono_set Set.inter_subset_left
  have hIimg : IntegrableOn (fun w => f ((A.chart b).symm w) * D b w)
      ((A.chart b ∘ (A.chart a).symm) ''
        ((A.chart a).target ∩ (A.chart a).symm ⁻¹' (A.chart b).source)) := by
    rw [ReciprocityTheory.AnForm.A.integrableOn_image_iff_analytic _ _ hU hτ hinj]
    refine hIU.congr_fun (fun z hz => ?_) hU.measurableSet
    simp only [smul_eq_mul]
    exact (heq z hz).symm
  refine ⟨hIimg.of_forall_sdiff_eq_zero (A.chart b).open_target.measurableSet hzero, ?_⟩
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (A.chart b).open_target.measurableSet
      himg hzero,
    ReciprocityTheory.AnForm.A.integral_image_eq_integral_normSq_det_smul _ _ hU hτ hinj]
  refine setIntegral_congr_fun hU.measurableSet (fun z hz => ?_)
  simp only [smul_eq_mul]
  exact heq z hz

theorem dI_chi_le_one (A : FinHolAtlas e X) (P : ChartPartition A) (k : Fin A.n) (x : X) :
    P.χ k x ≤ 1 := by
  calc P.χ k x ≤ ∑ j, P.χ j x := Finset.single_le_sum (fun j _ => P.nonneg j x) (Finset.mem_univ k)
    _ = 1 := P.sum_eq_one x

theorem dI_chi_contOn (A : FinHolAtlas e X) (P : ChartPartition A) (j k : Fin A.n) :
    ContinuousOn (fun y => P.χ j ((A.chart k).symm y)) (A.chart k).target := by
  have := (P.smooth j k).continuousOn
  simpa [Function.comp_def] using this

theorem dI_chi_zero (A : FinHolAtlas e X) (P : ChartPartition A) (j : Fin A.n) {x : X}
    (hx : x ∉ (A.chart j).source) : P.χ j x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (P.tsupport_subset j h))

theorem dI_bdd_mul (A : FinHolAtlas e X) (P : ChartPartition A) (j k : Fin A.n)
    {f : (Fin e → ℂ) → ℝ} (hf : IntegrableOn f (A.chart k).target) :
    IntegrableOn (fun y => P.χ j ((A.chart k).symm y) * f y) (A.chart k).target := by
  have hs : MeasurableSet (A.chart k).target := (A.chart k).open_target.measurableSet
  refine Integrable.bdd_mul (c := 1) hf ((dI_chi_contOn A P j k).aestronglyMeasurable hs) ?_
  exact Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (P.nonneg j _)]
    exact dI_chi_le_one A P j _

theorem dI_localize (A : FinHolAtlas e X) (P : ChartPartition A)
    {D : Fin A.n → (Fin e → ℂ) → ℝ} (hD : DIChartDens A D) (k : Fin A.n) (g : X → ℝ)
    (hg : ∀ x, x ∉ (A.chart k).source → g x = 0)
    (hint : IntegrableOn (fun z => g ((A.chart k).symm z) * D k z) (A.chart k).target) :
    (∀ j, IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * D j y)
      (A.chart j).target) ∧
    ∑ j, ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * D j y =
      ∫ z in (A.chart k).target, g ((A.chart k).symm z) * D k z := by
  have hfk : ∀ j, IntegrableOn (fun z => P.χ j ((A.chart k).symm z) * g ((A.chart k).symm z) *
      D k z) (A.chart k).target := by
    intro j
    have := dI_bdd_mul A P j k hint
    simpa only [mul_assoc] using this
  have hT : ∀ j, IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
        D j y) (A.chart j).target ∧
      ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * D j y =
        ∫ z in (A.chart k).target, P.χ j ((A.chart k).symm z) * g ((A.chart k).symm z) *
          D k z := by
    intro j
    obtain ⟨h1, h2⟩ := dI_transfer A hD k j (fun x => P.χ j x * g x)
      (fun x hx => by simp [hg x hx]) (hfk j)
    refine ⟨h1, h2.trans ?_⟩
    symm
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (A.chart k).open_target.measurableSet
      Set.inter_subset_left ?_
    rintro z ⟨hz, hzU⟩
    have : (A.chart k).symm z ∉ (A.chart j).source := fun h => hzU ⟨hz, h⟩
    simp [dI_chi_zero A P j this]
  refine ⟨fun j => (hT j).1, ?_⟩
  rw [Finset.sum_congr rfl (fun j _ => (hT j).2), ← integral_finsetSum _ (fun j _ => hfk j)]
  refine setIntegral_congr_fun (A.chart k).open_target.measurableSet (fun y _ => ?_)
  rw [← Finset.sum_mul, ← Finset.sum_mul, P.sum_eq_one, one_mul]

theorem dI_target_of_weights (A : FinHolAtlas e X) (P : ChartPartition A)
    {D : Fin A.n → (Fin e → ℂ) → ℝ} (hD : DIChartDens A D) (g : X → ℝ)
    (hw : ∀ j, IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
      D j y) (A.chart j).target) (k : Fin A.n) :
    IntegrableOn (fun y => g ((A.chart k).symm y) * D k y) (A.chart k).target := by
  have hj : ∀ j, IntegrableOn (fun y => P.χ j ((A.chart k).symm y) * g ((A.chart k).symm y) *
      D k y) (A.chart k).target := fun j =>
    (dI_transfer A hD j k (fun x => P.χ j x * g x)
      (fun x hx => by simp [dI_chi_zero A P j hx]) (hw j)).1
  have := integrable_finsetSum Finset.univ
    (f := fun j y => P.χ j ((A.chart k).symm y) * g ((A.chart k).symm y) * D k y)
    (fun j _ => hj j)
  refine IntegrableOn.congr_fun this (fun y _ => ?_) (A.chart k).open_target.measurableSet
  rw [← Finset.sum_mul, ← Finset.sum_mul, P.sum_eq_one, one_mul]

theorem dI_target_of_mIntegrable [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ) (hg : MIntegrable A Φ g)
    (k : Fin A.n) :
    IntegrableOn (fun y => g ((A.chart k).symm y) * locDens A Φ k y) (A.chart k).target := by
  obtain ⟨P⟩ := existsPartition A
  exact dI_target_of_weights A P (dI_chartDens_locDens A Φ hΦ) g
    (fun j => integrableOn_weight A P Φ g hg j) k

theorem dI_mset {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (φ : OpenPartialHomeomorph Z (Fin e → ℂ)) {s : Set Z} (hs : MeasurableSet s) :
    MeasurableSet (φ.target ∩ φ.symm ⁻¹' s) := by
  have hc : Continuous (φ.target.domRestrict φ.symm) := φ.continuousOn_symm.domRestrict
  have h1 := φ.open_target.measurableSet.subtype_image (hc.measurable hs)
  convert h1 using 1
  ext y
  constructor
  · rintro ⟨hy, hs'⟩; exact ⟨⟨y, hy⟩, hs', rfl⟩
  · rintro ⟨⟨y', hy'⟩, hs', rfl⟩; exact ⟨hy', hs'⟩

theorem dI_indicator {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (φ : OpenPartialHomeomorph Z (Fin e → ℂ)) {E : Set Z} (hE : MeasurableSet E) (g : Z → ℝ)
    (w : (Fin e → ℂ) → ℝ) (hint : IntegrableOn (fun z => g (φ.symm z) * w z) φ.target) :
    IntegrableOn (fun z => E.indicator g (φ.symm z) * w z) φ.target := by
  have h1 := hint.indicator (dI_mset φ hE)
  refine h1.congr_fun (fun z hz => ?_) φ.open_target.measurableSet
  by_cases h : φ.symm z ∈ E
  · rw [Set.indicator_of_mem (show z ∈ φ.target ∩ φ.symm ⁻¹' E from ⟨hz, h⟩),
      Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (show z ∉ φ.target ∩ φ.symm ⁻¹' E from fun h' => h h'.2),
      Set.indicator_of_notMem h, zero_mul]

theorem dI_hasSum [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) (G : X → ℝ)
    (hG : ∀ j, IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * G ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target)
    (E : ℕ → Set X) (hE : ∀ m, MeasurableSet (E m)) (hd : Pairwise (Function.onFun Disjoint E))
    (N : Set X) (hN : ∀ j, volume ((A.chart j) '' (N ∩ (A.chart j).source)) = 0)
    (hcov : (⋃ m, E m) = Nᶜ) :
    HasSum (fun m => integralWith A P Φ ((E m).indicator G)) (integralWith A P Φ G) := by
  unfold integralWith
  refine hasSum_sum (fun j _ => ?_)
  have hR : ∀ m, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' E m) :=
    fun m => dI_mset _ (hE m)
  have hRd : Pairwise (Function.onFun Disjoint
      fun m => (A.chart j).target ∩ (A.chart j).symm ⁻¹' E m) := by
    intro m m' hmm'
    exact ((hd hmm').preimage _).mono Set.inter_subset_right Set.inter_subset_right
  have hsub : (⋃ m, (A.chart j).target ∩ (A.chart j).symm ⁻¹' E m) ⊆ (A.chart j).target :=
    Set.iUnion_subset fun m => Set.inter_subset_left
  have H := hasSum_integral_iUnion hR hRd ((hG j).mono_set hsub)
  have h1 : ∀ m, ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) *
      (E m).indicator G ((A.chart j).symm y) * locDens A Φ j y =
      ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' E m, P.χ j ((A.chart j).symm y) *
        G ((A.chart j).symm y) * locDens A Φ j y := by
    intro m
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet
      Set.inter_subset_left ?_]
    · refine setIntegral_congr_fun (hR m) (fun y hy => ?_)
      rw [Set.indicator_of_mem (show (A.chart j).symm y ∈ E m from hy.2)]
    · rintro y ⟨hy, hyR⟩
      have : (A.chart j).symm y ∉ E m := fun h => hyR ⟨hy, h⟩
      simp [Set.indicator_of_notMem this]
  have h2 : ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) * G ((A.chart j).symm y) *
      locDens A Φ j y = ∫ y in ⋃ m, (A.chart j).target ∩ (A.chart j).symm ⁻¹' E m,
        P.χ j ((A.chart j).symm y) * G ((A.chart j).symm y) * locDens A Φ j y := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      (A.chart j).open_target.measurableSet.nullMeasurableSet hsub ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN j)] with y hy hyd
    exfalso
    apply hy
    have hyt := hyd.1
    have hnot : (A.chart j).symm y ∉ ⋃ m, E m := fun h => by
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 h
      exact hyd.2 (Set.mem_iUnion.2 ⟨m, hyt, hm⟩)
    rw [hcov, Set.mem_compl_iff, not_not] at hnot
    exact ⟨_, ⟨hnot, (A.chart j).map_target hyt⟩, (A.chart j).right_inv hyt⟩
  simp only [h1, h2]
  exact H

end

end ReciprocityTheory.AnForm.M
