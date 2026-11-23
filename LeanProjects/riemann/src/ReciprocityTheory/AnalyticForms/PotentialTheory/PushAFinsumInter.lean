import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem pushA_isClosed (A : FinHolAtlas e X) {S : Set X} (hS : A.IsAnalyticSubset S) :
    IsClosed S := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨W, hWo, hxW, r, f, hf, hSW⟩ := hS x
  have hx' : x ∉ {y ∈ W | ∀ i, f i y = 0} := by
    rw [← hSW]; exact fun h => hx h.1
  have hex : ∃ i, f i x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx' ⟨hxW, h⟩
  obtain ⟨i, hi⟩ := hex
  obtain ⟨k, hk⟩ := A.cover x
  have hcont : ContinuousAt (f i) x := by
    have han : AnalyticAt ℂ (f i ∘ (A.chart k).symm) (A.chart k x) :=
      hf i k _ ⟨(A.chart k).map_source hk, by simpa [(A.chart k).left_inv hk] using hxW⟩
    have h1 : ContinuousAt ((f i ∘ (A.chart k).symm) ∘ (A.chart k)) x :=
      ContinuousAt.comp (g := f i ∘ (A.chart k).symm) han.continuousAt
        ((A.chart k).continuousAt hk)
    refine h1.congr ?_
    filter_upwards [(A.chart k).open_source.mem_nhds hk] with y hy
    simp [(A.chart k).left_inv hy]
  have hN : {y | f i y ≠ 0} ∈ 𝓝 x := hcont.eventually_ne hi
  obtain ⟨N, hNsub, hNo, hxN⟩ := mem_nhds_iff.1 (inter_mem hN (hWo.mem_nhds hxW))
  refine ⟨N, fun y hy hyS => ?_, hNo, hxN⟩
  have : y ∈ S ∩ W := ⟨hyS, (hNsub hy).2⟩
  rw [hSW] at this
  exact (hNsub hy).1 (this.2 i)

theorem pushA_analytic (A : FinHolAtlas e X) {Q : Set X} {q : X → Fin e → ℂ}
    (hq : ∀ i, A.HoloOn Q (fun x => q x i)) (j : Fin A.n) {z : Fin e → ℂ}
    (hz : z ∈ (A.chart j).target) (hzQ : (A.chart j).symm z ∈ Q) :
    AnalyticAt ℂ (q ∘ (A.chart j).symm) z := by
  have := (analyticAt_pi_iff (f := fun i => (fun x => q x i) ∘ (A.chart j).symm) (e := z)).2
    (fun i => hq i j z ⟨hz, hzQ⟩)
  exact this

theorem pushA_det_comp (f g : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
    LinearMap.det ((f.comp g : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
        LinearMap.det (g : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
  exact LinearMap.det_comp (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) (g : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))

theorem pushA_dens (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    {Q : Set X} {q : X → Fin e → ℂ} (hq : ∀ i, A.HoloOn Q (fun x => q x i))
    (j : Fin A.n) {z : Fin e → ℂ} (hz : z ∈ (A.chart j).target) (hzQ : (A.chart j).symm z ∈ Q)
    (hdet : LinearMap.det (fderiv ℂ (q ∘ (A.chart (chartIdx A ((A.chart j).symm z))).symm)
        (A.chart (chartIdx A ((A.chart j).symm z)) ((A.chart j).symm z)) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) :
    Complex.normSq (LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) * pushDens A Φ q ((A.chart j).symm z) =
      locDens A Φ j z := by
  have hxc : (A.chart j).symm z ∈ (A.chart (chartIdx A ((A.chart j).symm z))).source :=
    Classical.choose_spec (A.cover ((A.chart j).symm z))
  have hch := locDensChart A Φ hΦ j (chartIdx A ((A.chart j).symm z)) z hz hxc
  have hτ : AnalyticAt ℂ (A.chart (chartIdx A ((A.chart j).symm z)) ∘ (A.chart j).symm) z :=
    A.holo j _ z ⟨hz, hxc⟩
  have hqc : AnalyticAt ℂ (q ∘ (A.chart (chartIdx A ((A.chart j).symm z))).symm)
      ((A.chart (chartIdx A ((A.chart j).symm z)) ∘ (A.chart j).symm) z) := by
    apply pushA_analytic A hq
    · exact (A.chart _).map_source hxc
    · simpa [(A.chart _).left_inv hxc] using hzQ
  have heq : q ∘ (A.chart j).symm =ᶠ[𝓝 z] (q ∘ (A.chart (chartIdx A ((A.chart j).symm z))).symm) ∘
      (A.chart (chartIdx A ((A.chart j).symm z)) ∘ (A.chart j).symm) := by
    have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (A.chart (chartIdx A ((A.chart j).symm z))).source ∈ 𝓝 z :=
      ((A.chart j).isOpen_inter_preimage_symm (A.chart _).open_source).mem_nhds ⟨hz, hxc⟩
    filter_upwards [hmem] with w hw
    simp [(A.chart _).left_inv hw.2]
  have hfd := heq.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_comp z hqc.differentiableAt hτ.differentiableAt] at hfd
  rw [hfd, hch, pushDens, pushA_det_comp, map_mul,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have ha := norm_ne_zero_iff.2 hdet
  simp only [Function.comp_apply] at ha ⊢
  field_simp

theorem pushA_detR (f : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
    (f.restrictScalars ℝ).det = Complex.normSq (LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) :=
  ReciprocityTheory.AnForm.A.det_restrictScalars_real (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))

theorem pushA_fib (q : X → Fin e → ℂ) (s : (Fin e → ℂ) → X) {D : Set (Fin e → ℂ)}
    (hinj : Set.InjOn (q ∘ s) D) :
    (∀ z ∈ D, q ⁻¹' {q (s z)} ∩ s '' D = {s z}) ∧
      ∀ y, y ∉ (q ∘ s) '' D → q ⁻¹' {y} ∩ s '' D = ∅ := by
  refine ⟨fun z hz => ?_, fun y hy => ?_⟩
  · ext x
    constructor
    · rintro ⟨hx1, z', hz', rfl⟩
      have h : (q ∘ s) z' = (q ∘ s) z := hx1
      rw [hinj hz' hz h]
      rfl
    · rintro rfl
      exact ⟨rfl, z, hz, rfl⟩
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image,
      Set.mem_empty_iff_false, iff_false, not_and, not_exists]
    rintro hx1 z' hz' rfl
    exact hy ⟨z', hz', hx1⟩

theorem pushA_piece (q : X → Fin e → ℂ) (s : (Fin e → ℂ) → X) {D : Set (Fin e → ℂ)}
    (hD : MeasurableSet D) (hdiff : ∀ z ∈ D, DifferentiableAt ℂ (q ∘ s) z)
    (hinj : Set.InjOn (q ∘ s) D) (k : X → ℝ) :
    (Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} ∩ s '' D, k x) ↔
      IntegrableOn (fun z => Complex.normSq (LinearMap.det (fderiv ℂ (q ∘ s) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) * k (s z)) D) ∧
    ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} ∩ s '' D, k x =
      ∫ z in D, Complex.normSq (LinearMap.det (fderiv ℂ (q ∘ s) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) * k (s z) := by
  obtain ⟨h1, h2⟩ := pushA_fib q s hinj
  set G : (Fin e → ℂ) → ℝ := fun y => ∑ᶠ x ∈ q ⁻¹' {y} ∩ s '' D, k x with hG
  have hGτ : ∀ z ∈ D, G ((q ∘ s) z) = k (s z) := by
    intro z hz
    simp only [hG]
    rw [Function.comp_apply, h1 z hz, finsum_mem_singleton]
  have hG0 : ∀ y, y ∉ (q ∘ s) '' D → G y = 0 := by
    intro y hy
    simp only [hG]
    rw [h2 y hy, finsum_mem_empty]
  have hf' : ∀ z ∈ D, HasFDerivWithinAt (q ∘ s) ((fderiv ℂ (q ∘ s) z).restrictScalars ℝ) D z :=
    fun z hz => ((hdiff z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hEq : Set.EqOn (fun z => |((fderiv ℂ (q ∘ s) z).restrictScalars ℝ).det| • G ((q ∘ s) z))
      (fun z => Complex.normSq (LinearMap.det (fderiv ℂ (q ∘ s) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) * k (s z)) D := by
    intro z hz
    simp only [smul_eq_mul]
    rw [hGτ z hz, pushA_detR, abs_of_nonneg (Complex.normSq_nonneg _)]
  have hI := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hD hf' hinj G
  have hJ := integral_image_eq_integral_abs_det_fderiv_smul volume hD hf' hinj G
  constructor
  · rw [← integrableOn_congr_fun hEq hD, ← hI]
    exact ⟨fun h => h.integrableOn, fun h => h.integrable_of_forall_notMem_eq_zero hG0⟩
  · rw [← setIntegral_congr_fun hD hEq, ← hJ, setIntegral_eq_integral_of_forall_compl_eq_zero hG0]

theorem pushA_piece_norm (q : X → Fin e → ℂ) (s : (Fin e → ℂ) → X) {D : Set (Fin e → ℂ)}
    (hinj : Set.InjOn (q ∘ s) D) (k : X → ℝ) (y : Fin e → ℂ) :
    ‖∑ᶠ x ∈ q ⁻¹' {y} ∩ s '' D, k x‖ = ∑ᶠ x ∈ q ⁻¹' {y} ∩ s '' D, |k x| := by
  obtain ⟨h1, h2⟩ := pushA_fib q s hinj
  by_cases hy : y ∈ (q ∘ s) '' D
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [Function.comp_apply, h1 z hz, finsum_mem_singleton, finsum_mem_singleton, Real.norm_eq_abs]
  · rw [h2 y hy, finsum_mem_empty, finsum_mem_empty, norm_zero]

theorem pushA_locInj {τ : (Fin e → ℂ) → (Fin e → ℂ)} {z : Fin e → ℂ} (hτ : AnalyticAt ℂ τ z)
    (hd : LinearMap.det (fderiv ℂ τ z : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) :
    ∃ W : Set (Fin e → ℂ), IsOpen W ∧ z ∈ W ∧ Set.InjOn τ W := by
  let L : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ) :=
    (LinearMap.equivOfDetNeZero (fderiv ℂ τ z : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) hd).toContinuousLinearEquiv
  have hL : (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = fderiv ℂ τ z := by
    ext v : 1
    simp [L]
  have hs : HasStrictFDerivAt τ (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) z := hL ▸ hτ.hasStrictFDerivAt
  refine ⟨(hs.toOpenPartialHomeomorph τ).source, (hs.toOpenPartialHomeomorph τ).open_source,
    hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  have := (hs.toOpenPartialHomeomorph τ).injOn
  simpa using this

theorem pushA_cover (O : Set (Fin e → ℂ)) (hO : IsOpen O) (τ : (Fin e → ℂ) → (Fin e → ℂ))
    (hloc : ∀ z ∈ O, ∃ W : Set (Fin e → ℂ), IsOpen W ∧ z ∈ W ∧ Set.InjOn τ W) :
    ∃ D : ℕ → Set (Fin e → ℂ), (∀ m, MeasurableSet (D m)) ∧ Pairwise (Function.onFun Disjoint D) ∧
      (⋃ m, D m) = O ∧ ∀ m, Set.InjOn τ (D m) := by
  set 𝒮 : Set (Set (Fin e → ℂ)) := {W | IsOpen W ∧ W ⊆ O ∧ Set.InjOn τ W}
  obtain ⟨T, hTc, hTS, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable 𝒮 (fun W hW => hW.1)
  have hU : ⋃₀ 𝒮 ⊆ O := fun z ⟨W, hW, hz⟩ => hW.2.1 hz
  have hU' : O ⊆ ⋃₀ 𝒮 := by
    intro z hz
    obtain ⟨W, hWo, hzW, hinj⟩ := hloc z hz
    exact ⟨W ∩ O, ⟨hWo.inter hO, Set.inter_subset_right, hinj.mono Set.inter_subset_left⟩,
      ⟨hzW, hz⟩⟩
  have hUeq : ⋃₀ T = O := hTU.trans (subset_antisymm hU hU')
  have hT'c : (insert (∅ : Set (Fin e → ℂ)) T).Countable := hTc.insert ∅
  obtain ⟨f, hf⟩ := hT'c.exists_eq_range (Set.insert_nonempty _ _)
  have hfS : ∀ m, f m ∈ 𝒮 := by
    intro m
    have hm : f m ∈ insert (∅ : Set (Fin e → ℂ)) T := by rw [hf]; exact Set.mem_range_self m
    rcases hm with h | h
    · rw [h]; exact ⟨isOpen_empty, Set.empty_subset _, Set.injOn_empty _⟩
    · exact hTS h
  refine ⟨disjointed f, fun m => MeasurableSet.disjointed (fun i => (hfS i).1.measurableSet) m,
    disjoint_disjointed f, ?_, fun m => (hfS m).2.2.mono (disjointed_subset f m)⟩
  rw [iUnion_disjointed, ← Set.sUnion_range, ← hf, Set.sUnion_insert, Set.empty_union, hUeq]

theorem pushA_intOn [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) (g : X → ℝ) (hg : MIntegrable A Φ g) (j : Fin A.n) :
    IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target := by
  have hK : IsCompact ((A.chart j) '' tsupport (P.χ j)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((A.chart j).continuousOn.mono (P.tsupport_subset j))
  have hKt : (A.chart j) '' tsupport (P.χ j) ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (P.tsupport_subset j hx)
  have hcont : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
    have := (P.smooth j j).continuousOn
    simpa [Function.comp_def] using this
  have h1 := (hg j _ hKt hK).continuousOn_mul (hcont.mono hKt) hK
  simp_rw [mul_assoc]
  refine h1.of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet ?_
  rintro y ⟨hy, hyK⟩
  have : P.χ j ((A.chart j).symm y) = 0 := by
    by_contra hne
    exact hyK ⟨_, subset_tsupport _ hne, (A.chart j).right_inv hy⟩
  rw [this, zero_mul]

theorem pushA_intTsum {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : ℕ → α → ℝ}
    (hF : ∀ i, Integrable (F i) μ) (hsum : ∀ a, Summable fun i => F i a)
    (hs : Summable fun i => ∫ a, ‖F i a‖ ∂μ) : Integrable (fun a => ∑' i, F i a) μ := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (fun N => (integrable_finsetSum (Finset.range N) fun i _ => hF i).aestronglyMeasurable)
    (Eventually.of_forall fun a => (hsum a).hasSum.tendsto_sum_nat), ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ :=
        lintegral_mono fun a => enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ := lintegral_tsum fun i => (hF i).aestronglyMeasurable.enorm
    _ = ∑' i, ENNReal.ofReal (∫ a, ‖F i a‖ ∂μ) := by
        congr 1; funext i; rw [ofReal_integral_norm_eq_lintegral_enorm (hF i)]
    _ = ENNReal.ofReal (∑' i, ∫ a, ‖F i a‖ ∂μ) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun a => norm_nonneg _) hs).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem pushA_hasSum_ind (E : ℕ → Set X) (hE : Pairwise (Function.onFun Disjoint E)) (f : X → ℝ)
    (x : X) : HasSum (fun m => (E m).indicator f x) ((⋃ m, E m).indicator f x) := by
  by_cases hx : ∃ m0, x ∈ E m0
  · obtain ⟨m0, hm0⟩ := hx
    have hne : ∀ m, m ≠ m0 → (E m).indicator f x = 0 := by
      intro m hm
      exact Set.indicator_of_notMem (fun h => Set.disjoint_left.1 (hE hm) h hm0) f
    rw [Set.indicator_of_mem (Set.mem_iUnion.2 ⟨m0, hm0⟩), ← Set.indicator_of_mem hm0 f]
    exact hasSum_single m0 hne
  · push Not at hx
    rw [Set.indicator_of_notMem (by simpa using hx)]
    have : (fun m => (E m).indicator f x) = fun _ => 0 :=
      funext fun m => Set.indicator_of_notMem (hx m) f
    rw [this]
    exact hasSum_zero

theorem pushA_sum_finsum {ι : Type*} [Fintype ι] {F : Set X} (hF : F.Finite) (h : ι → X → ℝ) :
    ∑ i, ∑ᶠ x ∈ F, h i x = ∑ᶠ x ∈ F, ∑ i, h i x := by
  simp only [finsum_mem_eq_finite_toFinset_sum _ hF]
  exact Finset.sum_comm

theorem pushA_finsum_inter (F E : Set X) (f : X → ℝ) :
    ∑ᶠ x ∈ F ∩ E, f x = ∑ᶠ x ∈ F, E.indicator f x := by
  rw [finsum_mem_def, finsum_mem_def, Set.indicator_indicator]

end

end ReciprocityTheory.AnForm.M
