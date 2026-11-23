import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibGlue

noncomputable section

namespace PI.VolStabSW.DiscreteGroups

open MeasureTheory Topology Set Filter PI.VolStabSW PI.VolStabSW.Glue
open scoped ENNReal

section

variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V]

theorem cover (U : Set V) (hU : IsOpen U) : ∃ W : ℕ → Set V,
    (∀ n, IsOpen (W n) ∧ IsCompact (closure (W n)) ∧ closure (W n) ⊆ U) ∧ ⋃ n, W n = U := by
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let E := CompactExhaustion.choice U
  have h : ∀ n, ∃ W, IsOpen W ∧ Subtype.val '' E n ⊆ W ∧ closure W ⊆ U ∧ IsCompact (closure W) :=
    fun n => exists_open_between_and_isCompact_closure ((E.isCompact n).image continuous_subtype_val)
      hU (by rintro _ ⟨u, -, rfl⟩; exact u.2)
  choose W hW1 hW2 hW3 hW4 using h
  refine ⟨W, fun n => ⟨hW1 n, hW4 n, hW3 n⟩,
    subset_antisymm (iUnion_subset fun n => subset_closure.trans (hW3 n)) ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := E.exists_mem ⟨x, hx⟩
  exact mem_iUnion.2 ⟨n, hW2 n ⟨_, hn, rfl⟩⟩

theorem approx (O : Set V) (hO : IsOpen O) : ∃ φ : ℕ → V → ℝ,
    (∀ k, Continuous (φ k) ∧ HasCompactSupport (φ k) ∧ tsupport (φ k) ⊆ O) ∧
    (∀ k x, 0 ≤ φ k x ∧ φ k x ≤ 1) ∧ (∀ x, Monotone fun k => φ k x) ∧
    ∀ x, ⨆ k, ENNReal.ofReal (φ k x) = O.indicator 1 x := by
  haveI : LocallyCompactSpace O := hO.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let E := CompactExhaustion.choice O
  have h : ∀ k, ∃ g : C(V, ℝ), EqOn g 1 (Subtype.val '' E k) ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ Subtype.val '' interior (E (k + 1)) ∧ ∀ x, g x ∈ Icc (0 : ℝ) 1 := fun k =>
    exists_continuousMap_one_of_isCompact_subset_isOpen ((E.isCompact k).image continuous_subtype_val)
      (hO.isOpenMap_subtype_val _ isOpen_interior) (image_mono (E.subset_interior_succ k))
  choose g hg1 hgc hgs hg01 using h
  have hsubO : ∀ k, tsupport (g k) ⊆ O :=
    fun k => (hgs k).trans (by rintro _ ⟨u, -, rfl⟩; exact u.2)
  have hmono : ∀ x, Monotone fun k => g k x := by
    intro x
    refine monotone_nat_of_le_succ fun k => ?_
    by_cases hx : x ∈ tsupport (g k)
    · obtain ⟨u, hu, rfl⟩ := hgs k hx
      rw [hg1 (k + 1) ⟨u, interior_subset hu, rfl⟩]
      exact (hg01 k _).2
    · rw [image_eq_zero_of_notMem_tsupport hx]
      exact (hg01 (k + 1) x).1
  refine ⟨fun k => g k, fun k => ⟨(g k).continuous, hgc k, hsubO k⟩, fun k x => hg01 k x, hmono,
    fun x => ?_⟩
  by_cases hx : x ∈ O
  · obtain ⟨n, hn⟩ := E.exists_mem ⟨x, hx⟩
    rw [indicator_of_mem hx]
    apply le_antisymm
    · refine iSup_le fun k => ?_
      have := ENNReal.ofReal_le_ofReal (hg01 k x).2
      simpa using this
    · refine le_iSup_of_le n ?_
      have h1 : g n x = 1 := hg1 n ⟨⟨x, hx⟩, hn, rfl⟩
      show (1 : V → ℝ≥0∞) x ≤ ENNReal.ofReal (g n x)
      rw [h1]
      simp
  · rw [indicator_of_notMem hx]
    simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hsubO _ h))]

variable {X Y : Type} [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}
  (hf : Continuous f) (hι : IsClosedEmbedding ι) (hr : ∀ v, f v ∈ Set.range ι) (hU : IsOpen U)
  (h0 : ∀ b, fib b (f ⁻¹' {ι b} ∩ U)ᶜ = 0) (h2 : ∀ b K, IsCompact K → K ⊆ U → fib b K < ⊤)
  (h3 : ∀ φ : V → ℝ, IsCcOn U φ → (∀ b, Integrable φ (fib b)) ∧
        Continuous (fun b => ∫ v, φ v ∂(fib b)) ∧
        ∀ S : Set X, IsCompact S → ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, ∫ v, φ v ∂(fib b) ∂ν)

include hf hι hr hU h0 h2 h3

theorem cc_case (ψ : V → ℝ) (hψ : IsCcOn U ψ) (h0ψ : ∀ v, 0 ≤ ψ v) :
    ∫⁻ v, ENNReal.ofReal (ψ v) ∂μ = ∫⁻ b, ∫⁻ v, ENNReal.ofReal (ψ v) ∂(fib b) ∂ν := by
  obtain ⟨hint, hcont, hS⟩ := h3 ψ hψ
  set S : Set X := ι ⁻¹' (f '' tsupport ψ) with hSdef
  have hSc : IsCompact S := hι.isCompact_preimage (hψ.2.1.image hf)
  have hsub : tsupport ψ ⊆ f ⁻¹' (ι '' S) := by
    intro v hv
    obtain ⟨s, hs⟩ := hr v
    exact ⟨s, ⟨v, hv, hs.symm⟩, hs⟩
  have hzero : ∀ b ∉ S, ∫ v, ψ v ∂(fib b) = 0 := by
    intro b hb
    apply integral_eq_zero_of_ae
    have hae : ∀ᵐ v ∂(fib b), v ∉ (f ⁻¹' {ι b} ∩ U)ᶜ := measure_eq_zero_iff_ae_notMem.1 (h0 b)
    filter_upwards [hae] with v hv
    simp only [mem_compl_iff, not_not] at hv
    exact (eq_or_ne (ψ v) 0).resolve_right fun hne => hb ⟨v, subset_tsupport _ hne, hv.1⟩
  have e1 : ∫ v in f ⁻¹' (ι '' S), ψ v ∂μ = ∫ v, ψ v ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv =>
      image_eq_zero_of_notMem_tsupport fun h => hv (hsub h)
  have e2 : ∫ b in S, (∫ v, ψ v ∂(fib b)) ∂ν = ∫ b, (∫ v, ψ v ∂(fib b)) ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun b hb => hzero b hb
  have hG : Integrable (fun b => ∫ v, ψ v ∂(fib b)) ν :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro' hSc hSc.isClosed hzero)
  have hi : Integrable ψ μ := hψ.1.integrable_of_hasCompactSupport hψ.2.1
  calc ∫⁻ v, ENNReal.ofReal (ψ v) ∂μ = ENNReal.ofReal (∫ v, ψ v ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ h0ψ)).symm
    _ = ENNReal.ofReal (∫ b, (∫ v, ψ v ∂(fib b)) ∂ν) := by rw [← e1, hS S hSc, e2]
    _ = ∫⁻ b, ENNReal.ofReal (∫ v, ψ v ∂(fib b)) ∂ν :=
        ofReal_integral_eq_lintegral_ofReal hG
          (ae_of_all _ fun b => integral_nonneg fun v => h0ψ v)
    _ = ∫⁻ b, ∫⁻ v, ENNReal.ofReal (ψ v) ∂(fib b) ∂ν :=
        lintegral_congr fun b => ofReal_integral_eq_lintegral_ofReal (hint b) (ae_of_all _ h0ψ)

theorem open_case (O : Set V) (hO : IsOpen O) (hOU : O ⊆ U) :
    Measurable (fun b => fib b O) ∧ μ O = ∫⁻ b, fib b O ∂ν := by
  obtain ⟨φ, hφ, h01, hmono, hlim⟩ := approx O hO
  have hcc : ∀ k, IsCcOn U (φ k) := fun k => ⟨(hφ k).1, (hφ k).2.1, (hφ k).2.2.trans hOU⟩
  have hmeas : ∀ k, Measurable fun v => ENNReal.ofReal (φ k v) :=
    fun k => ENNReal.measurable_ofReal.comp (hφ k).1.measurable
  have hmon : Monotone fun k v => ENNReal.ofReal (φ k v) :=
    fun i j hij v => ENNReal.ofReal_le_ofReal (hmono v hij)
  have hfibO : ∀ b, fib b O = ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) := by
    intro b
    rw [← lintegral_iSup hmeas hmon]
    simp_rw [hlim]
    rw [lintegral_indicator_one hO.measurableSet]
  have hk : ∀ k, Measurable fun b => ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) := by
    intro k
    have : (fun b => ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b)) =
        fun b => ENNReal.ofReal (∫ v, φ k v ∂(fib b)) :=
      funext fun b => (ofReal_integral_eq_lintegral_ofReal ((h3 _ (hcc k)).1 b)
        (ae_of_all _ fun v => (h01 k v).1)).symm
    rw [this]
    exact ENNReal.measurable_ofReal.comp (h3 _ (hcc k)).2.1.measurable
  have hmonb : Monotone fun k b => ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) :=
    fun i j hij b => lintegral_mono fun v => ENNReal.ofReal_le_ofReal (hmono v hij)
  refine ⟨?_, ?_⟩
  · simp_rw [hfibO]
    exact Measurable.iSup hk
  · calc μ O = ∫⁻ v, O.indicator 1 v ∂μ := (lintegral_indicator_one hO.measurableSet).symm
      _ = ∫⁻ v, ⨆ k, ENNReal.ofReal (φ k v) ∂μ := by simp_rw [hlim]
      _ = ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂μ := lintegral_iSup hmeas hmon
      _ = ⨆ k, ∫⁻ b, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) ∂ν := by
          congr 1; funext k
          exact cc_case hf hι hr hU h0 h2 h3 (φ k) (hcc k) fun v => (h01 k v).1
      _ = ∫⁻ b, ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) ∂ν := (lintegral_iSup hk hmonb).symm
      _ = ∫⁻ b, fib b O ∂ν := by simp_rw [hfibO]

theorem null_compl (b : X) : fib b Uᶜ = 0 :=
  measure_mono_null (compl_subset_compl.2 inter_subset_right) (h0 b)

theorem meas_fib : ∀ A, MeasurableSet A → Measurable fun b => fib b A := by
  obtain ⟨W, hW, hWU⟩ := cover U hU
  have hWsub : ∀ n, W n ⊆ U := fun n => subset_closure.trans (hW n).2.2
  have hfin : ∀ b n, fib b (W n) ≠ ⊤ := fun b n =>
    (lt_of_le_of_lt (measure_mono subset_closure) (h2 b _ (hW n).2.1 (hW n).2.2)).ne
  have hP : ∀ n, ∀ A, MeasurableSet A → Measurable fun b => fib b (A ∩ W n) := by
    intro n
    refine MeasurableSpace.induction_on_inter
      (C := fun A _ => Measurable fun b => fib b (A ∩ W n)) (s := {s : Set V | IsOpen s})
      BorelSpace.measurable_eq isPiSystem_isOpen ?_ ?_ ?_ ?_
    · simp only [empty_inter, measure_empty]; exact measurable_const
    · intro t ht
      exact (open_case hf hι hr hU h0 h2 h3 (t ∩ W n) ((ht : IsOpen t).inter (hW n).1)
        (inter_subset_right.trans (hWsub n))).1
    · intro t htm IH
      have e : ∀ b, fib b (tᶜ ∩ W n) = fib b (W n) - fib b (t ∩ W n) := by
        intro b
        rw [← measure_diff inter_subset_right (htm.inter (hW n).1.measurableSet).nullMeasurableSet
          ((measure_mono inter_subset_right).trans_lt (lt_top_iff_ne_top.2 (hfin b n))).ne]
        congr 1
        ext x
        simp only [mem_inter_iff, mem_compl_iff, mem_diff]
        tauto
      simp_rw [e]
      exact (open_case hf hι hr hU h0 h2 h3 (W n) (hW n).1 (hWsub n)).1.sub IH
    · intro g hd hgm IH
      have e : ∀ b, fib b ((⋃ i, g i) ∩ W n) = ∑' i, fib b (g i ∩ W n) := by
        intro b
        rw [iUnion_inter, measure_iUnion (fun i j hij => (hd hij).mono inter_subset_left
          inter_subset_left) (fun i => (hgm i).inter (hW n).1.measurableSet)]
      simp_rw [e]
      exact Measurable.ennreal_tsum IH
  intro A hA
  have hD : ∀ n, MeasurableSet (disjointed W n) :=
    MeasurableSet.disjointed fun n => (hW n).1.measurableSet
  have e : ∀ b, fib b A = ∑' n, fib b (A ∩ disjointed W n) := by
    intro b
    rw [← measure_inter_add_diff A hU.measurableSet,
      measure_mono_null (show A \ U ⊆ Uᶜ from fun x hx => hx.2) (null_compl hf hι hr hU h0 h2 h3 b),
      add_zero,
      ← hWU, ← iUnion_disjointed, inter_iUnion,
      measure_iUnion (fun i j hij => ((disjoint_disjointed W) hij).mono inter_subset_right
        inter_subset_right) (fun n => hA.inter (hD n))]
  simp_rw [e]
  refine Measurable.ennreal_tsum fun n => ?_
  have := hP n (A ∩ disjointed W n) (hA.inter (hD n))
  simpa only [inter_eq_left.2 (inter_subset_right.trans (disjointed_subset W n))] using this

end

theorem disintStep_holds : DisintStep := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν hμ hν hpos f ι U hf hι hr hU fib h0 h2 h3 φ hφ
  have hmf : Measurable fib :=
    Measure.measurable_of_measurable_coe fib (meas_fib hf hι hr hU h0 h2 h3)
  have hρ : μ.restrict U = ν.bind fib := by
    obtain ⟨B, hB, hBU⟩ := cover (univ : Set V) isOpen_univ
    refine Measure.ext_of_generateFrom_of_iUnion {s : Set V | IsOpen s} B BorelSpace.measurable_eq
      isPiSystem_isOpen hBU (fun i => (hB i).1) (fun i => ?_) ?_
    · exact ((Measure.restrict_apply_le _ _).trans_lt
        ((measure_mono subset_closure).trans_lt (hB i).2.1.measure_lt_top)).ne
    · intro s hs
      rw [Measure.restrict_apply (hs : IsOpen s).measurableSet,
        Measure.bind_apply hs.measurableSet hmf.aemeasurable,
        (open_case hf hι hr hU h0 h2 h3 (s ∩ U) (hs.inter hU) inter_subset_right).2]
      congr 1
      funext b
      rw [← measure_inter_add_diff s hU.measurableSet,
        measure_mono_null (show s \ U ⊆ Uᶜ from fun x hx => hx.2)
          (null_compl hf hι hr hU h0 h2 h3 b), add_zero]
  rw [hρ, Measure.lintegral_bind hmf.aemeasurable hφ.aemeasurable]

theorem fibOfDens_holds : FibOfDens := fibOfDens_of disintStep_holds

end PI.VolStabSW.DiscreteGroups
