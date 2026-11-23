import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal Pointwise

namespace GlobalTheory.QuotientHaar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

theorem measurable_translate (g : G) : Measurable (fun h : H => g * (h : G)) :=
  (continuous_const.mul continuous_subtype_val).measurable

noncomputable def cosetMeasure (ν : Measure H) [ν.IsMulLeftInvariant] : G ⧸ H → Measure G :=
  Quotient.lift (fun g : G => ν.map (fun h : H => g * (h : G))) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have h1 := map_mul_left_eq_self ν (⟨a⁻¹ * b, hab'⟩ : H)
    beta_reduce
    conv_lhs => rw [← h1]
    rw [Measure.map_map (measurable_translate H a) (measurable_const_mul _)]
    congr 1
    funext h
    simp [← mul_assoc])

theorem cosetMeasure_mk (ν : Measure H) [ν.IsMulLeftInvariant] (g : G) :
    cosetMeasure H ν (g : G ⧸ H) = ν.map (fun h : H => g * (h : G)) := rfl

theorem cosetMeasure_apply (ν : Measure H) [ν.IsMulLeftInvariant] (g : G) {s : Set G}
    (hs : MeasurableSet s) :
    cosetMeasure H ν (g : G ⧸ H) s = ν ((fun h : H => g * (h : G)) ⁻¹' s) := by
  rw [cosetMeasure_mk, Measure.map_apply (measurable_translate H g) hs]

theorem lintegral_cosetMeasure (ν : Measure H) [ν.IsMulLeftInvariant] {f : G → ℝ≥0∞}
    (hf : Measurable f) (q : G ⧸ H) :
    ∫⁻ x, f x ∂(cosetMeasure H ν q) = fibreIntegral H ν f q := by
  induction q using QuotientGroup.induction_on with
  | H g => rw [cosetMeasure_mk, lintegral_map hf (measurable_translate H g), fibreIntegral_mk]

variable [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem cosetMeasure_lt_top (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsHaarMeasure]
    (q : G ⧸ H) {K : Set G} (hK : IsCompact K) : cosetMeasure H ν q K < ⊤ := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [cosetMeasure_apply H ν g hK.measurableSet]
    have h1 : IsCompact ((fun x : G => g * x) ⁻¹' K) :=
      (Homeomorph.mulLeft g).isCompact_preimage.mpr hK
    exact (hH.isClosedEmbedding_subtypeVal.isCompact_preimage h1).measure_lt_top

theorem measurable_cosetMeasure_open (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] {U : Set G}
    (hU : IsOpen U) : Measurable (fun q : G ⧸ H => cosetMeasure H ν q U) := by
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : ν.Regular := inferInstance
  refine measurable_of_Ioi fun c => IsOpen.measurableSet ?_
  rw [← (QuotientGroup.isQuotientMap_mk H).isOpen_preimage, isOpen_iff_mem_nhds]
  intro g hg
  simp only [Set.mem_preimage, Set.mem_Ioi, cosetMeasure_apply H ν g hU.measurableSet] at hg
  have hO : IsOpen ((fun h : H => g * (h : G)) ⁻¹' U) :=
    hU.preimage (continuous_const.mul continuous_subtype_val)
  obtain ⟨K, hKU, hK, hc⟩ := hO.exists_lt_isCompact hg
  have hev : ∀ᶠ x in nhds g, ∀ h ∈ K, x * (h : G) ∈ U := by
    refine hK.eventually_forall_of_forall_eventually fun h hh => ?_
    have hcont : Continuous (fun p : G × H => p.1 * (p.2 : G)) := by fun_prop
    exact hcont.continuousAt.eventually_mem (hU.mem_nhds (hKU hh))
  filter_upwards [hev] with x hx
  simp only [Set.mem_preimage, Set.mem_Ioi, cosetMeasure_apply H ν x hU.measurableSet]
  exact hc.trans_le (measure_mono fun h hh => hx h hh)

theorem measurable_cosetMeasure (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] :
    Measurable (cosetMeasure H ν) := by
  let K := CompactExhaustion.choice G
  have hres : ∀ n, Measurable (fun q => (cosetMeasure H ν q).restrict (interior (K n))) := by
    intro n
    haveI : ∀ q, IsFiniteMeasure ((cosetMeasure H ν q).restrict (interior (K n))) := fun q =>
      isFiniteMeasure_restrict.mpr ((measure_mono interior_subset).trans_lt
        (cosetMeasure_lt_top H hH ν q (K.isCompact n))).ne
    have key : ∀ s : Set G, IsOpen s →
        Measurable fun q => (cosetMeasure H ν q).restrict (interior (K n)) s := by
      intro s hs
      simp only [Measure.restrict_apply hs.measurableSet]
      exact measurable_cosetMeasure_open H hH ν (hs.inter isOpen_interior)
    exact Measurable.measure_of_isPiSystem (S := {s : Set G | IsOpen s})
      BorelSpace.measurable_eq isPiSystem_isOpen key (key _ isOpen_univ)
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hmono : Monotone fun n => s ∩ interior (K n) := fun a b hab =>
    Set.inter_subset_inter_right _ (interior_mono (K.subset hab))
  have hun : ⋃ n, s ∩ interior (K n) = s := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    refine ⟨fun ⟨_, h, _⟩ => h, fun h => ?_⟩
    obtain ⟨n, hn⟩ := K.exists_mem x
    exact ⟨n + 1, h, K.subset_interior_succ n hn⟩
  have : (fun q => cosetMeasure H ν q s) =
      fun q => ⨆ n, (cosetMeasure H ν q).restrict (interior (K n)) s := by
    funext q
    simp only [Measure.restrict_apply hs]
    rw [← hmono.measure_iUnion, hun]
  rw [this]
  exact Measurable.iSup fun n => (Measure.measurable_coe hs).comp (hres n)

theorem measurable_fibreIntegral (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] {f : G → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fibreIntegral H ν f) := by
  have : fibreIntegral H ν f = fun q => ∫⁻ x, f x ∂(cosetMeasure H ν q) :=
    funext fun q => (lintegral_cosetMeasure H ν hf q).symm
  rw [this]
  exact (Measure.measurable_lintegral hf).comp (measurable_cosetMeasure H hH ν)

theorem quotientFormula_bind (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] (μ : Measure (G ⧸ H)) :
    QuotientFormula H (μ.bind (cosetMeasure H ν)) ν μ := by
  intro f hf
  refine ⟨measurable_fibreIntegral H hH ν hf, ?_⟩
  rw [Measure.lintegral_bind (measurable_cosetMeasure H hH ν).aemeasurable hf.aemeasurable]
  exact lintegral_congr fun q => lintegral_cosetMeasure H ν hf q

theorem isHaarMeasure_bind (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] (μ : Measure (G ⧸ H))
    (hμ : IsInvariantRadon H μ) : (μ.bind (cosetMeasure H ν)).IsHaarMeasure := by
  haveI := hμ.finiteOnCompacts
  haveI := hμ.invariant
  have hm := measurable_cosetMeasure H hH ν
  haveI hfin : IsFiniteMeasureOnCompacts (μ.bind (cosetMeasure H ν)) := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.bind_apply hK.measurableSet hm.aemeasurable]
    have hC : ν (Subtype.val ⁻¹' (K⁻¹ * K)) < ⊤ :=
      (hH.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.inv.mul hK)).measure_lt_top
    have hπ : IsCompact ((QuotientGroup.mk : G → G ⧸ H) '' K) :=
      hK.image QuotientGroup.continuous_mk
    have hle : ∀ q, cosetMeasure H ν q K ≤ ((QuotientGroup.mk : G → G ⧸ H) '' K).indicator
        (fun _ => ν (Subtype.val ⁻¹' (K⁻¹ * K))) q := by
      intro q
      by_cases hq : q ∈ (QuotientGroup.mk : G → G ⧸ H) '' K
      · rw [Set.indicator_of_mem hq]
        obtain ⟨k, hk, rfl⟩ := hq
        rw [cosetMeasure_apply H ν k hK.measurableSet]
        refine measure_mono fun h hh => ?_
        exact ⟨k⁻¹, Set.inv_mem_inv.mpr hk, k * h, hh, by simp⟩
      · induction q using QuotientGroup.induction_on with
        | H g =>
          rw [cosetMeasure_apply H ν g hK.measurableSet]
          have : (fun h : H => g * (h : G)) ⁻¹' K = ∅ :=
            Set.eq_empty_of_forall_notMem fun h hh => hq ⟨g * h, hh, by simp⟩
          simp [this]
    refine (lintegral_mono hle).trans_lt ((lintegral_indicator_const_le _ _).trans_lt ?_)
    exact ENNReal.mul_lt_top hC hπ.measure_lt_top
  haveI hinv : (μ.bind (cosetMeasure H ν)).IsMulLeftInvariant := by
    refine (forall_measure_preimage_mul_iff _).mp fun a s hs => ?_
    rw [Measure.bind_apply hs hm.aemeasurable,
      Measure.bind_apply (measurable_const_mul a hs) hm.aemeasurable]
    have h1 : Measurable fun q => cosetMeasure H ν q s := (Measure.measurable_coe hs).comp hm
    have h2 := (measurePreserving_smul a μ).lintegral_comp h1
    rw [← h2]
    refine lintegral_congr fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H g =>
      change _ = cosetMeasure H ν ((a * g : G) : G ⧸ H) s
      rw [cosetMeasure_apply H ν g (measurable_const_mul a hs), cosetMeasure_apply H ν _ hs]
      congr 1
      ext h
      simp [mul_assoc]
  have hne : μ.bind (cosetMeasure H ν) ≠ 0 := by
    intro h0
    have h1 : μ.bind (cosetMeasure H ν) Set.univ = ν Set.univ * μ Set.univ := by
      rw [Measure.bind_apply MeasurableSet.univ hm.aemeasurable, ← lintegral_const]
      refine lintegral_congr fun q => ?_
      induction q using QuotientGroup.induction_on with
      | H g => rw [cosetMeasure_apply H ν g MeasurableSet.univ, Set.preimage_univ]
    rw [h0] at h1
    exact mul_ne_zero (isOpen_univ.measure_ne_zero ν Set.univ_nonempty)
      (Measure.measure_univ_ne_zero.mpr hμ.ne_zero) h1.symm
  haveI : IsLocallyFiniteMeasure (μ.bind (cosetMeasure H ν)) :=
    isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : NeZero (μ.bind (cosetMeasure H ν)) := ⟨hne⟩
  haveI : (μ.bind (cosetMeasure H ν)).IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_regular
  exact {}

end GlobalTheory.QuotientHaar

namespace GlobalTheory.QuotientHaar

theorem existsUnique_haar_of_invariantRadon : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)], IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure] (μ : Measure (G ⧸ H)), IsInvariantRadon H μ → ∃! dg : Measure G, dg.IsHaarMeasure ∧ QuotientFormula H dg ν μ := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH ν _ μ hμ
  refine ⟨μ.bind (cosetMeasure H ν),
    ⟨isHaarMeasure_bind H hH ν μ hμ, quotientFormula_bind H hH ν μ⟩, fun dg hdg => ?_⟩
  ext s hs
  have hf : Measurable (s.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, (hdg.2 _ hf).2,
    (quotientFormula_bind H hH ν μ _ hf).2]

end GlobalTheory.QuotientHaar
