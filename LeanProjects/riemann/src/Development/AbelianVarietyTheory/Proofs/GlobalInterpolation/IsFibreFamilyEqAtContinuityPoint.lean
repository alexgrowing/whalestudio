import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Set Topology
open scoped ENNReal

namespace GlobalTheory

open MeasureTheory Set Topology in
open scoped ENNReal in
private lemma exists_compact_exhaustion_with_bumps {V : Type} [MetricSpace V] [ProperSpace V]
    {G : Set V} (hG : IsOpen G) :
    ∃ (K : ℕ → Set V) (f : ℕ → C(V, ℝ)), Monotone K ∧ ⋃ n, K n = G ∧
      ∀ n, IsCompact (K n) ∧ EqOn (f n) 1 (K n) ∧ IsCompact (tsupport (f n)) ∧
        tsupport (f n) ⊆ G ∧ ∀ v, f n v ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  let E := CompactExhaustion.choice V
  let K : ℕ → Set V := fun n => F n ∩ E n
  have hKm : Monotone K := fun a b hab => inter_subset_inter (hFm hab) (E.subset hab)
  have hKU : ⋃ n, K n = G := by
    apply Subset.antisymm
    · exact iUnion_subset fun n => inter_subset_left.trans (hFG n)
    · intro x hx
      rw [← hFU] at hx
      obtain ⟨a, ha⟩ := mem_iUnion.1 hx
      obtain ⟨b, hb⟩ := E.exists_mem x
      exact mem_iUnion.2 ⟨max a b, hFm (le_max_left a b) ha, E.subset (le_max_right a b) hb⟩
  have hKc : ∀ n, IsCompact (K n) := fun n => (E.isCompact n).inter_left (hFc n)
  choose f hf1 hfc hfG hf01 using fun n =>
    exists_continuousMap_one_of_isCompact_subset_isOpen (hKc n) hG
      (inter_subset_left.trans (hFG n))
  exact ⟨K, f, hKm, hKU, fun n => ⟨hKc n, hf1 n, hfc n, hfG n, hf01 n⟩⟩

open MeasureTheory Set Topology in
open scoped ENNReal in
private lemma measure_le_lintegral_of_eqOn_one {V : Type} [MeasurableSpace V] (μ : Measure V)
    {K : Set V} (hK : MeasurableSet K) {g : V → ℝ} (hg : EqOn g 1 K) :
    μ K ≤ ∫⁻ v, ENNReal.ofReal (g v) ∂μ := by
  rw [← lintegral_indicator_one hK]
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ K
  · simp [indicator_of_mem hv, hg hv]
  · simp [indicator_of_notMem hv]

open MeasureTheory Set Topology in
open scoped ENNReal in
private lemma measure_isOpen_le_of_lintegral_le {V : Type} [MetricSpace V] [ProperSpace V]
    [MeasurableSpace V] [BorelSpace V] (m m' : Measure V) {G : Set V} (hG : IsOpen G)
    (h : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ G → (∀ v, 0 ≤ φ v) →
      ∫⁻ v, ENNReal.ofReal (φ v) ∂m ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂m') :
    m G ≤ m' G := by
  obtain ⟨K, f, hKm, hKU, hKf⟩ := exists_compact_exhaustion_with_bumps hG
  have hGK : m G = ⨆ n, m (K n) := by rw [← hKm.measure_iUnion, hKU]
  rw [hGK]
  refine iSup_le fun n => ?_
  obtain ⟨hKc, hf1, hfc, hfG, hf01⟩ := hKf n
  calc m (K n) ≤ ∫⁻ v, ENNReal.ofReal (f n v) ∂m :=
        measure_le_lintegral_of_eqOn_one m hKc.isClosed.measurableSet hf1
    _ ≤ ∫⁻ v, ENNReal.ofReal (f n v) ∂m' :=
        h (f n) (f n).continuous hfc hfG fun v => (hf01 v).1
    _ ≤ ∫⁻ v, G.indicator 1 v ∂m' := by
        refine lintegral_mono fun v => ?_
        by_cases hv : v ∈ G
        · simp [indicator_of_mem hv, (hf01 v).2]
        · have : f n v = 0 := image_eq_zero_of_notMem_tsupport fun h' => hv (hfG h')
          simp [this]
    _ = m' G := lintegral_indicator_one hG.measurableSet

open MeasureTheory Set Topology in
open scoped ENNReal in

theorem _root_.GlobalTheory.measure_eq_of_lintegral_eq_on_compactSupport {V : Type} [MetricSpace V] [ProperSpace V]
    [MeasurableSpace V] [BorelSpace V] (m m' : Measure V) (O : Set V) (hO : IsOpen O)
    (hm : m Oᶜ = 0) (hm' : m' Oᶜ = 0)
    (h : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O → (∀ v, 0 ≤ φ v) →
      Integrable φ m ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂m = ∫⁻ v, ENNReal.ofReal (φ v) ∂m') :
    m = m' := by
  have hopen : ∀ G : Set V, IsOpen G → G ⊆ O → m G = m' G := fun G hG hGO =>
    le_antisymm
      (measure_isOpen_le_of_lintegral_le m m' hG fun φ hc hs ht hn =>
        (h φ hc hs (ht.trans hGO) hn).2.le)
      (measure_isOpen_le_of_lintegral_le m' m hG fun φ hc hs ht hn =>
        (h φ hc hs (ht.trans hGO) hn).2.ge)
  obtain ⟨K, f, -, hKU, hKf⟩ := exists_compact_exhaustion_with_bumps hO
  let W : Option ℕ → Set V := fun i => i.elim Oᶜ fun n => {v | 0 < f n v}
  have hWU : ⋃ i, W i = univ := by
    refine eq_univ_of_forall fun v => ?_
    by_cases hv : v ∈ O
    · rw [← hKU] at hv
      obtain ⟨n, hn⟩ := mem_iUnion.1 hv
      exact mem_iUnion.2 ⟨some n, show 0 < f n v by simp [(hKf n).2.1 hn]⟩
    · exact mem_iUnion.2 ⟨none, hv⟩
  rw [Measure.ext_iff_of_iUnion_eq_univ hWU]
  rintro (_ | n)
  · simp [W, Measure.restrict_eq_zero.2 hm, Measure.restrict_eq_zero.2 hm']
  · obtain ⟨-, -, hfc, hfO, -⟩ := hKf n
    have hWo : IsOpen {v | 0 < f n v} := isOpen_lt continuous_const (f n).continuous
    have hsub : {v | 0 < f n v} ⊆ tsupport (f n) := fun v hv =>
      subset_tsupport _ (ne_of_gt (show 0 < f n v from hv))
    have hWO : {v | 0 < f n v} ⊆ O := hsub.trans hfO
    obtain ⟨g, hg1, hgc, hgO, hg01⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hfc hO hfO
    have hfin : m {v | 0 < f n v} < ∞ :=
      (measure_mono hsub).trans_lt <|
        (measure_le_lintegral_of_eqOn_one m hfc.isClosed.measurableSet hg1).trans_lt
          (h g g.continuous hgc hgO fun v => (hg01 v).1).1.lintegral_lt_top
    haveI : IsFiniteMeasure (m.restrict {v | 0 < f n v}) := isFiniteMeasure_restrict.2 hfin.ne
    show m.restrict {v | 0 < f n v} = m'.restrict {v | 0 < f n v}
    refine ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen
      (fun s hs => ?_) ?_
    · rw [Measure.restrict_apply hs.measurableSet, Measure.restrict_apply hs.measurableSet]
      exact hopen _ (hs.inter hWo) (inter_subset_right.trans hWO)
    · simpa using hopen _ hWo hWO

open MeasureTheory Set Topology in
open scoped ENNReal in

theorem _root_.GlobalTheory.IsFibreFamily_lintegral_preimage {V : Type} [TopologicalSpace V]
    [MeasurableSpace V] [BorelSpace V] {μ : Measure V} {f : V → ℝ} {O U : Set V} {B : Set ℝ}
    {fib : ℝ → Measure V}
    (hf : Measurable f) (hO : IsOpen O) (hU : O ⊆ U)
    (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f id U (volume : Measure ℝ) B fib)
    (φ : V → ℝ≥0∞) (hφ : Measurable φ) (hs : ∀ v, v ∉ O → φ v = 0)
    (S : Set ℝ) (hS : MeasurableSet S) :
    ∫⁻ v in O, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h
  obtain ⟨hfib, hint, -⟩ := h
  have hψ : Measurable ((f ⁻¹' S).indicator φ) := hφ.indicator (hf hS)
  have hsupp : Function.support ((f ⁻¹' S).indicator φ) ⊆ O := by
    intro v hv
    by_contra hvO
    exact hv (by simp [indicator, hs v hvO])
  rw [setLIntegral_eq_of_support_subset hsupp,
    ← setLIntegral_eq_of_support_subset (hsupp.trans hU), hint _ hψ, ← lintegral_indicator hS]
  refine lintegral_congr fun b => ?_
  have hae : ∀ᵐ v ∂(fib b), f v = b := by
    refine ae_iff.2 (measure_mono_null ?_ (hfib b))
    intro v hv hv'
    exact hv hv'.1
  by_cases hb : b ∈ S
  · rw [indicator_of_mem hb]
    exact lintegral_congr_ae (hae.mono fun v hv => by simp [indicator, hv, hb])
  · rw [indicator_of_notMem hb]
    exact (lintegral_congr_ae (hae.mono fun v hv => by simp [indicator, hv, hb])).trans
      lintegral_zero

open MeasureTheory Set Topology in
open scoped ENNReal in
private lemma le_of_setLIntegral_eq_near {g g' : ℝ → ℝ} {β : ℝ} {W : Set ℝ} (hW : W ∈ 𝓝 β)
    (hg : ContinuousAt g β) (hg' : ContinuousAt g' β) (hg0 : 0 ≤ g' β)
    (h : ∀ S ⊆ W, MeasurableSet S →
      ∫⁻ b in S, ENNReal.ofReal (g b) = ∫⁻ b in S, ENNReal.ofReal (g' b)) :
    g β ≤ g' β := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c₁, h₁, h₂⟩ := exists_between hlt
  obtain ⟨c₂, h₃, h₄⟩ := exists_between h₂
  have e₁ : ∀ᶠ b in 𝓝 β, g' b < c₁ := hg'.eventually (gt_mem_nhds h₁)
  have e₂ : ∀ᶠ b in 𝓝 β, c₂ < g b := hg.eventually (lt_mem_nhds h₄)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hW (e₁.and e₂))
  have hS : MeasurableSet (Metric.ball β ε) := measurableSet_ball
  have hpos : volume (Metric.ball β ε) ≠ 0 := (Metric.measure_ball_pos volume β hε).ne'
  have hfin : volume (Metric.ball β ε) ≠ ∞ := measure_ball_lt_top.ne
  have low : ENNReal.ofReal c₂ * volume (Metric.ball β ε) ≤
      ∫⁻ b in Metric.ball β ε, ENNReal.ofReal (g b) := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall
      fun b hb => ENNReal.ofReal_le_ofReal (hball hb).2.2.le))
  have up : ∫⁻ b in Metric.ball β ε, ENNReal.ofReal (g' b) ≤
      ENNReal.ofReal c₁ * volume (Metric.ball β ε) := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall
      fun b hb => ENNReal.ofReal_le_ofReal (hball hb).2.1.le))
  have key := low.trans ((h _ (fun b hb => (hball hb).1) hS).le.trans up)
  have key' : ENNReal.ofReal c₂ ≤ ENNReal.ofReal c₁ := (ENNReal.mul_le_mul_iff_left hpos hfin).1 key
  rw [ENNReal.ofReal_le_ofReal_iff (hg0.trans h₁.le)] at key'
  exact absurd key' (not_le.2 h₃)

open MeasureTheory Set Topology in
open scoped ENNReal in

theorem _root_.GlobalTheory.IsFibreFamily_eq_at {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (f : V → ℝ)
    (O U U' : Set V) (B B' : Set ℝ) (fib fib' : ℝ → Measure V) (β : ℝ)
    (hf : Measurable f) (hO : IsOpen O) (hU : O ⊆ U) (hU' : O ⊆ U') (hβ : f ⁻¹' {β} ⊆ O)
    (hB : IsOpen B) (hB' : IsOpen B') (hβB : β ∈ B) (hβB' : β ∈ B')
    (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f id U (volume : Measure ℝ) B fib)
    (h' : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f id U' (volume : Measure ℝ) B' fib') : fib β = fib' β := by
  have hdens := fun (S : Set ℝ) (hS : MeasurableSet S) (φ : V → ℝ≥0∞) (hφ : Measurable φ)
      (hs : ∀ v, v ∉ O → φ v = 0) =>
    (_root_.GlobalTheory.IsFibreFamily_lintegral_preimage hf hO hU h φ hφ hs S hS).symm.trans
      (_root_.GlobalTheory.IsFibreFamily_lintegral_preimage hf hO hU' h' φ hφ hs S hS)
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h h'
  obtain ⟨hfib, -, hcts⟩ := h
  obtain ⟨hfib', -, hcts'⟩ := h'
  have hnull : Oᶜ ⊆ (f ⁻¹' {id β} ∩ U)ᶜ := compl_subset_compl.2 (inter_subset_left.trans hβ)
  have hnull' : Oᶜ ⊆ (f ⁻¹' {id β} ∩ U')ᶜ := compl_subset_compl.2 (inter_subset_left.trans hβ)
  refine _root_.GlobalTheory.measure_eq_of_lintegral_eq_on_compactSupport _ _ O hO (measure_mono_null hnull (hfib β))
    (measure_mono_null hnull' (hfib' β)) fun φ hφc hφs hφO hφ0 => ?_
  obtain ⟨hi, hc⟩ := hcts φ hφc hφs (hφO.trans hU)
  obtain ⟨hi', hc'⟩ := hcts' φ hφc hφs (hφO.trans hU')
  refine ⟨hi β hβB, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal (hi β hβB) (Filter.Eventually.of_forall hφ0),
    ← ofReal_integral_eq_lintegral_ofReal (hi' β hβB') (Filter.Eventually.of_forall hφ0)]
  have hW : B ∩ B' ∈ 𝓝 β := Filter.inter_mem (hB.mem_nhds hβB) (hB'.mem_nhds hβB')
  have hφm : Measurable fun v => ENNReal.ofReal (φ v) := hφc.measurable.ennreal_ofReal
  have hφz : ∀ v, v ∉ O → ENNReal.ofReal (φ v) = 0 := fun v hv => by
    rw [image_eq_zero_of_notMem_tsupport fun h'' => hv (hφO h'')]
    simp
  have hset : ∀ S ⊆ B ∩ B', MeasurableSet S →
      ∫⁻ b in S, ENNReal.ofReal (∫ v, φ v ∂fib b) =
        ∫⁻ b in S, ENNReal.ofReal (∫ v, φ v ∂fib' b) := by
    intro S hSW hS
    rw [setLIntegral_congr_fun hS fun b hb =>
        ofReal_integral_eq_lintegral_ofReal (hi b (hSW hb).1) (Filter.Eventually.of_forall hφ0),
      setLIntegral_congr_fun hS fun b hb =>
        ofReal_integral_eq_lintegral_ofReal (hi' b (hSW hb).2) (Filter.Eventually.of_forall hφ0)]
    exact hdens S hS _ hφm hφz
  have hca := hc.continuousAt (hB.mem_nhds hβB)
  have hca' := hc'.continuousAt (hB'.mem_nhds hβB')
  congr 1
  exact le_antisymm
    (le_of_setLIntegral_eq_near hW hca hca' (integral_nonneg hφ0) hset)
    (le_of_setLIntegral_eq_near hW hca' hca (integral_nonneg hφ0) fun S hSW hS =>
      (hset S hSW hS).symm)

end GlobalTheory
