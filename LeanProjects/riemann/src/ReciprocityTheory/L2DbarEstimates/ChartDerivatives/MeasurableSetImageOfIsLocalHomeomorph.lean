import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

section VolAux

variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M]

theorem measurableSet_image_of_chart (n : ℕ) (z : M → V n) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) (S : Set M) (hS : MeasurableSet S) (hSe : S ⊆ e.source) :
    MeasurableSet (z '' S) := by
  have h1 : z '' S = e '' S := Set.image_congr (fun x hx => he (hSe hx))
  have h2 : e '' S = e.target ∩ e.symm ⁻¹' S := by
    have h3 := e.image_source_inter_eq' S
    rwa [Set.inter_eq_right.mpr hSe] at h3
  rw [h1, h2]
  have hm : MeasurableSet ((e.target).restrict e.symm ⁻¹' S) :=
    (e.continuousOn_symm.restrict).measurable hS
  have h4 := e.open_target.measurableSet.subtype_image hm
  convert h4 using 1
  ext w
  simp [Set.restrict, and_comm]

theorem exists_chart_cover (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) :
    ∃ T : ℕ → Set M, (∀ i, IsOpen (T i)) ∧ (⋃ i, T i = univ) ∧
      ∀ i, T i = ∅ ∨ ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ T i ⊆ e.source := by
  classical
  have hz' : ∀ x, ∃ e : OpenPartialHomeomorph M (V n), x ∈ e.source ∧ z = e := hz
  choose e hxe hze using hz'
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x => (e x).source)
    (fun x => (e x).open_source)
  have hmem : ∀ x, x ∈ ⋃ y ∈ T, (e y).source := by
    intro x; rw [hTU]; exact Set.mem_iUnion.2 ⟨x, hxe x⟩
  by_cases hT : T.Nonempty
  · obtain ⟨g, hg⟩ := hTc.exists_eq_range hT
    refine ⟨fun i => (e (g i)).source, fun i => (e (g i)).open_source, ?_,
      fun i => Or.inr ⟨e (g i), fun w _ => congrFun (hze (g i)) w, subset_rfl⟩⟩
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨y, hyT, hy⟩ := Set.mem_iUnion₂.1 (hmem x)
    rw [hg] at hyT
    obtain ⟨i, rfl⟩ := hyT
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  · refine ⟨fun _ => ∅, fun _ => isOpen_empty, ?_, fun _ => Or.inl rfl⟩
    rw [Set.not_nonempty_iff_eq_empty] at hT
    ext x
    exfalso
    have h1 := hmem x
    rw [hT] at h1
    simp at h1

theorem measurableSet_image_of_isLocalHomeomorph (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z)
    (A : Set M) (hA : MeasurableSet A) : MeasurableSet (z '' A) := by
  obtain ⟨T, hTo, hTU, hTc⟩ := exists_chart_cover n z hz
  have h1 : A = ⋃ i, A ∩ T i := by rw [← Set.inter_iUnion, hTU, Set.inter_univ]
  rw [h1, Set.image_iUnion]
  refine MeasurableSet.iUnion (fun i => ?_)
  rcases hTc i with h | ⟨e, he, hTe⟩
  · simp [h]
  · exact measurableSet_image_of_chart n z e he _ (hA.inter (hTo i).measurableSet)
      (Set.inter_subset_right.trans hTe)

omit [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in

theorem encard_inter_fiber_of_injOn (n : ℕ) (z : M → V n) (S : Set M) (hS : InjOn z S) (y : V n) :
    (((S ∩ z ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) = (z '' S).indicator 1 y := by
  by_cases hy : y ∈ z '' S
  · obtain ⟨a, ha, rfl⟩ := hy
    have h1 : S ∩ z ⁻¹' {z a} = {a} := by
      ext b
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hb, hba⟩; exact hS hb ha hba
      · rintro rfl; exact ⟨ha, rfl⟩
    rw [h1, Set.encard_singleton]
    simp [Set.indicator_apply, Set.mem_image_of_mem z ha]
  · have h1 : S ∩ z ⁻¹' {y} = ∅ := by
      ext b
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro hb hby
      exact hy ⟨b, hb, hby⟩
    rw [h1, Set.encard_empty]
    simp [Set.indicator_apply, hy]

end VolAux

section VolMain

variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M]

omit [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in

theorem injOn_source_of_chart (n : ℕ) (z : M → V n) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) : InjOn z e.source := by
  intro a ha b hb hab
  exact e.injOn ha hb (by rw [← he ha, ← he hb]; exact hab)

private theorem encard_eq_count {X : Type*} [MeasurableSpace X] (S : Set X) (hS : MeasurableSet S) :
    ((S.encard : ℕ∞) : ℝ≥0∞) = Measure.count S := by
  rw [Measure.count_apply hS]
  all_goals first | rfl | simp

theorem measurable_encard_fiber (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (A : Set M)
    (hA : MeasurableSet A) :
    Measurable fun y => (((A ∩ z ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) := by
  obtain ⟨T, hTo, hTU, hTc⟩ := exists_chart_cover n z hz
  have hmz : ∀ y : V n, MeasurableSet (z ⁻¹' {y}) :=
    fun y => (measurableSet_singleton y).preimage hz.continuous.measurable
  have hDm : ∀ i, MeasurableSet (disjointed T i) :=
    MeasurableSet.disjointed (fun i => (hTo i).measurableSet)
  have hDd : Pairwise (Function.onFun Disjoint (disjointed T)) := disjoint_disjointed T
  have hDU : ⋃ i, disjointed T i = Set.univ := by rw [iUnion_disjointed, hTU]
  have hDT : ∀ i, disjointed T i ⊆ T i := disjointed_subset T
  have injA : ∀ i, InjOn z (A ∩ disjointed T i) := by
    intro i
    rcases hTc i with h | ⟨e, he, hTe⟩
    · have h2 : A ∩ disjointed T i = ∅ :=
        Set.subset_empty_iff.mp (Set.inter_subset_right.trans ((hDT i).trans h.subset))
      rw [h2]; exact Set.injOn_empty z
    · exact (injOn_source_of_chart n z e he).mono
        (Set.inter_subset_right.trans ((hDT i).trans hTe))
  have key : ∀ y, ((A ∩ z ⁻¹' {y}).encard : ℝ≥0∞) =
      ∑' i, (z '' (A ∩ disjointed T i)).indicator 1 y := by
    intro y
    have h3 : A ∩ z ⁻¹' {y} = ⋃ i, (A ∩ disjointed T i) ∩ z ⁻¹' {y} := by
      rw [← Set.iUnion_inter, ← Set.inter_iUnion, hDU, Set.inter_univ]
    rw [encard_eq_count _ (hA.inter (hmz y)), h3,
      measure_iUnion (fun i j hij => ((show Disjoint (disjointed T i) (disjointed T j) from hDd hij).mono
        (Set.inter_subset_left.trans Set.inter_subset_right)
        (Set.inter_subset_left.trans Set.inter_subset_right)))
        (fun i => (hA.inter (hDm i)).inter (hmz y))]
    congr 1
    funext i
    rw [← encard_eq_count _ ((hA.inter (hDm i)).inter (hmz y)),
      encard_inter_fiber_of_injOn n z _ (injA i) y]
  have h4 : (fun y => ((A ∩ z ⁻¹' {y}).encard : ℝ≥0∞)) =
      fun y => ∑' i, (z '' (A ∩ disjointed T i)).indicator 1 y := funext key
  rw [h4]
  exact Measurable.ennreal_tsum (fun i => measurable_one.indicator
    (measurableSet_image_of_isLocalHomeomorph n z hz _ (hA.inter (hDm i))))

end VolMain

theorem volAdditive {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) :
    VolAdditive n z := by
  intro f hf hd
  have hmz : ∀ y : V n, MeasurableSet (z ⁻¹' {y}) :=
    fun y => (measurableSet_singleton y).preimage hz.continuous.measurable
  simp only [volFun]
  have h1 : ∀ y, (((⋃ i, f i) ∩ z ⁻¹' {y}).encard : ℝ≥0∞) =
      ∑' i, ((f i ∩ z ⁻¹' {y}).encard : ℝ≥0∞) := by
    intro y
    rw [encard_eq_count _ ((MeasurableSet.iUnion hf).inter (hmz y)), Set.iUnion_inter,
      measure_iUnion (fun i j hij => ((show Disjoint (f i) (f j) from hd hij).mono
        Set.inter_subset_left Set.inter_subset_left)) (fun i => (hf i).inter (hmz y))]
    congr 1
    funext i
    rw [encard_eq_count _ ((hf i).inter (hmz y))]
  simp_rw [h1]
  exact lintegral_tsum (fun i => (measurable_encard_fiber n z hz (f i) (hf i)).aemeasurable)

theorem vol_apply {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (A : Set M) (hA : MeasurableSet A) :
    vol n z A = volFun n z A := by
  rw [vol, dif_pos (volAdditive n z hz), Measure.ofMeasurable_apply A hA]

theorem vol_image {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (U : Set M) (hU : IsOpen U) (hinj : InjOn z U) (A : Set M) (hA : MeasurableSet A) (hAU : A ⊆ U) :
    vol n z A = volume (z '' A) := by
  rw [vol_apply n z hz A hA, volFun]
  have hinjA : InjOn z A := hinj.mono hAU
  simp_rw [encard_inter_fiber_of_injOn n z A hinjA]
  rw [lintegral_indicator_one (measurableSet_image_of_isLocalHomeomorph n z hz A hA)]

theorem vol_restrict_source {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) :
    (vol n z).restrict e.source = Measure.map e.symm (volume.restrict e.target) := by
  ext B hB
  rw [Measure.restrict_apply hB,
    Measure.map_apply_of_aemeasurable
      (e.continuousOn_symm.aemeasurable e.open_target.measurableSet) hB,
    Measure.restrict_apply' e.open_target.measurableSet,
    vol_image n z hz e.source e.open_source (injOn_source_of_chart n z e he) _
      (hB.inter e.open_source.measurableSet) Set.inter_subset_right]
  congr 1
  rw [Set.image_congr (fun x hx => he hx.2), Set.inter_comm B e.source,
    e.image_source_inter_eq']
  exact Set.inter_comm _ _

theorem lintegral_vol_chart {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (f : M → ℝ≥0∞) (hf : Measurable f) (hs : ∀ x, x ∉ e.source → f x = 0) :
    ∫⁻ x, f x ∂vol n z = ∫⁻ y in e.target, f (e.symm y) := by
  have h1 : ∫⁻ x, f x ∂vol n z = ∫⁻ x in e.source, f x ∂vol n z := by
    rw [← lintegral_indicator e.open_source.measurableSet]
    congr 1
    funext x
    by_cases hx : x ∈ e.source
    · simp [Set.indicator_apply, hx]
    · simp [Set.indicator_apply, hx, hs x hx]
  rw [h1, vol_restrict_source n z hz e he,
    lintegral_map' hf.aemeasurable (e.continuousOn_symm.aemeasurable e.open_target.measurableSet)]

theorem integral_vol_chart {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (f : M → ℂ) (hf : Measurable f) (hs : ∀ x, x ∉ e.source → f x = 0) :
    ∫ x, f x ∂vol n z = ∫ y in e.target, f (e.symm y) := by
  have h1 : ∫ x, f x ∂vol n z = ∫ x in e.source, f x ∂vol n z := by
    rw [← integral_indicator e.open_source.measurableSet]
    congr 1
    funext x
    by_cases hx : x ∈ e.source
    · simp [Set.indicator_apply, hx]
    · simp [Set.indicator_apply, hx, hs x hx]
  rw [h1, vol_restrict_source n z hz e he,
    integral_map (e.continuousOn_symm.aemeasurable e.open_target.measurableSet)
      hf.aestronglyMeasurable]

theorem vol_isFiniteMeasureOnCompacts {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) :
    IsFiniteMeasureOnCompacts (vol n z) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨T, hTo, hTU, hTc⟩ := exists_chart_cover n z hz
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover T hTo (by rw [hTU]; exact Set.subset_univ K)
  have hzK : volume (z '' K) < ⊤ := (hK.image hz.continuous).measure_lt_top
  calc vol n z K ≤ vol n z (⋃ i ∈ s, K ∩ T i) := by
        refine measure_mono (fun x hx => ?_)
        have h1 := hs hx
        simp only [Set.mem_iUnion] at h1 ⊢
        obtain ⟨i, hi, hxi⟩ := h1
        exact ⟨i, hi, hx, hxi⟩
    _ ≤ ∑ i ∈ s, vol n z (K ∩ T i) := measure_biUnion_finset_le s _
    _ < ⊤ := by
        refine ENNReal.sum_lt_top.2 (fun i _ => ?_)
        rcases hTc i with h | ⟨e, he, hTe⟩
        · simp [h]
        · rw [vol_image n z hz e.source e.open_source (injOn_source_of_chart n z e he) _
            (hK.isClosed.measurableSet.inter (hTo i).measurableSet)
            (Set.inter_subset_right.trans hTe)]
          exact lt_of_le_of_lt (measure_mono (Set.image_mono Set.inter_subset_left)) hzK

end

end ReciprocityTheory.L2DbarEstimates
