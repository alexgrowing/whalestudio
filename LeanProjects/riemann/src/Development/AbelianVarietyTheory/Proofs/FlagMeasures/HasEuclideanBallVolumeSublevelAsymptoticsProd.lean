import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Filter Topology
open scoped ENNReal

namespace GlobalTheory.LeviIso

def SublevelLe {X X' : Type} [MeasurableSpace X] [MeasurableSpace X'] (c : ℝ≥0∞) (T : ℝ)
    (μ : Measure X) (q : X → ℝ) (μ' : Measure X') (q' : X' → ℝ) : Prop :=
  ∀ t ≤ T, μ {x | q x ≤ t} ≤ c * μ' {x | q' x ≤ t}

theorem SublevelLe.mono {X X' : Type} [MeasurableSpace X] [MeasurableSpace X'] {c : ℝ≥0∞}
    {T T' : ℝ} {μ : Measure X} {q : X → ℝ} {μ' : Measure X'} {q' : X' → ℝ}
    (h : SublevelLe c T μ q μ' q') (hT : T' ≤ T) : SublevelLe c T' μ q μ' q' :=
  fun t ht => h t (ht.trans hT)

theorem SublevelLe.prod {X X' Y Y' : Type} [MeasurableSpace X] [MeasurableSpace X']
    [MeasurableSpace Y] [MeasurableSpace Y'] {c : ℝ≥0∞} {T : ℝ}
    {μ : Measure X} {q : X → ℝ} {μ' : Measure X'} {q' : X' → ℝ}
    {ν : Measure Y} {p : Y → ℝ} {ν' : Measure Y'} {p' : Y' → ℝ}
    [SFinite μ] [SFinite μ'] [SFinite ν] [SFinite ν'] (hc : c ≠ ⊤)
    (hq : Measurable q) (hq' : Measurable q') (hp : Measurable p) (hp' : Measurable p')
    (hq0 : ∀ x, 0 ≤ q' x) (hp0 : ∀ y, 0 ≤ p y)
    (h1 : SublevelLe c T μ q μ' q') (h2 : SublevelLe c T ν p ν' p') :
    SublevelLe (c * c) T (μ.prod ν) (fun z => q z.1 + p z.2) (μ'.prod ν')
      (fun z => q' z.1 + p' z.2) := by
  intro t ht
  have m1 : MeasurableSet {z : X × Y | q z.1 + p z.2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have m2 : MeasurableSet {z : X' × Y | q' z.1 + p z.2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have m3 : MeasurableSet {z : X' × Y' | q' z.1 + p' z.2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have s1 : (μ.prod ν) {z : X × Y | q z.1 + p z.2 ≤ t}
      ≤ c * (μ'.prod ν) {z : X' × Y | q' z.1 + p z.2 ≤ t} := by
    rw [Measure.prod_apply_symm m1, Measure.prod_apply_symm m2, ← lintegral_const_mul' _ _ hc]
    refine lintegral_mono fun y => ?_
    have := h1 (t - p y) (by linarith [hp0 y])
    simpa only [Set.preimage_setOf_eq, le_sub_iff_add_le] using this
  have s2 : (μ'.prod ν) {z : X' × Y | q' z.1 + p z.2 ≤ t}
      ≤ c * (μ'.prod ν') {z : X' × Y' | q' z.1 + p' z.2 ≤ t} := by
    rw [Measure.prod_apply m2, Measure.prod_apply m3, ← lintegral_const_mul' _ _ hc]
    refine lintegral_mono fun x => ?_
    have := h2 (t - q' x) (by linarith [hq0 x])
    simpa only [Set.preimage_setOf_eq, le_sub_iff_add_le'] using this
  calc _ ≤ _ := s1
    _ ≤ c * (c * _) := by gcongr
    _ = _ := by rw [mul_assoc]

theorem volume_norm_sq_le (d : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    volume {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ r ^ 2}
      = ENNReal.ofReal (r ^ d) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  have : {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ r ^ 2} = Metric.closedBall 0 r := by
    ext u
    simp [sq_le_sq₀ (norm_nonneg u) hr]
  rw [this, Measure.addHaar_closedBall _ _ hr]
  simp

theorem setOf_sqrt_le {X : Type} (q : X → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    {x | √(q x) ≤ r} = {x | q x ≤ r ^ 2} := by
  ext x
  simp [Real.sqrt_le_left hr, Real.sqrt_le_iff, hr]

theorem volume_prod_norm_sq_le (d e : ℕ) (t : ℝ) :
    ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod
      (volume : Measure (EuclideanSpace ℝ (Fin e)))) {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ t}
      = volume {u : EuclideanSpace ℝ (Fin (d + e)) | ‖u‖ ^ 2 ≤ t} := by
  let f : WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (d + e)) :=
    ((stdOrthonormalBasis ℝ _).reindex (finCongr (by
      rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq]; simp))).repr
  have h := f.measurePreserving.comp (WithLp.volume_preserving_toLp _ _)
  rw [← h.measure_preimage (measurableSet_le (by fun_prop) measurable_const).nullMeasurableSet]
  congr 1
  ext z
  simp [WithLp.prod_norm_sq_eq_of_L2]

theorem exists_one_lt_mul_mul_lt {a b : ℝ≥0∞} (h : a < b) :
    ∃ c : ℝ≥0∞, 1 < c ∧ c ≠ ⊤ ∧ c * c * a < b := by
  have ha : a ≠ ⊤ := h.ne_top
  have t1 : Tendsto (fun c : ℝ≥0∞ => c * c * a) (𝓝 1) (𝓝 (1 * 1 * a)) :=
    ENNReal.Tendsto.mul_const
      (ENNReal.Tendsto.mul tendsto_id (by simp) tendsto_id (by simp)) (Or.inr ha)
  simp only [one_mul] at t1
  have e1 := t1.eventually (gt_mem_nhds h)
  have e2 : ∀ᶠ c : ℝ≥0∞ in 𝓝 1, c < ⊤ := gt_mem_nhds (by simp)
  haveI : (𝓝[>] (1 : ℝ≥0∞)).NeBot := nhdsGT_neBot_of_exists_gt ⟨⊤, by simp⟩
  obtain ⟨c, ⟨h1, h2⟩, h3⟩ := (((e1.and e2).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (1 : ℝ≥0∞)) (a := 1))).exists
  exact ⟨c, h3, h2.ne, h1⟩

theorem IsRadial.sublevelLe {X : Type} [MeasurableSpace X] {μ : Measure X} {q : X → ℝ} {d : ℕ}
    (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x) (h : IsRadial μ q d) {c : ℝ≥0∞} (hc : 1 < c)
    (hc' : c ≠ ⊤) :
    ∃ T > 0, SublevelLe c T μ q volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) ∧
      SublevelLe c T volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) μ q := by
  unfold IsRadial at h
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω
  have ω0 : ω ≠ 0 := (Metric.measure_ball_pos _ _ one_pos).ne'
  have ωt : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hlt : ω < c * ω := by
    simpa using ENNReal.mul_lt_mul_left ω0 ωt hc
  have e1 := h.eventually (gt_mem_nhds hlt)
  have e2 := (ENNReal.Tendsto.const_mul (a := c) h (Or.inl ω0)).eventually (lt_mem_nhds hlt)
  have e3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ {x | √(q x) ≤ r} ≤ c * (ENNReal.ofReal (r ^ d) * ω) ∧
      ENNReal.ofReal (r ^ d) * ω ≤ c * μ {x | √(q x) ≤ r} := by
    filter_upwards [e1, e2, self_mem_nhdsWithin] with r h1 h2 hr
    have hr' : (0 : ℝ) < r := hr
    have n0 : ENNReal.ofReal (r ^ d) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    constructor
    · have := (ENNReal.div_le_iff n0 ENNReal.ofReal_ne_top).1 h1.le
      calc _ ≤ _ := this
        _ = _ := by ring
    · rw [← mul_div_assoc] at h2
      have := (ENNReal.le_div_iff_mul_le (Or.inl n0) (Or.inl ENNReal.ofReal_ne_top)).1 h2.le
      rwa [mul_comm] at this
  have tg : Tendsto (fun r : ℝ => μ {x | √(q x) ≤ r}) (𝓝[>] 0) (𝓝 (μ {x | √(q x) ≤ 0})) := by
    have hI : {x | √(q x) ≤ 0} = ⋂ r > (0 : ℝ), {x | √(q x) ≤ r} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h r hr => h.trans hr.le, fun h => le_of_forall_gt_imp_ge_of_dense h⟩
    rw [hI]
    refine tendsto_measure_biInter_gt (s := fun r : ℝ => {x | √(q x) ≤ r})
      (fun r _ => (measurableSet_le (by fun_prop) measurable_const).nullMeasurableSet)
      (fun i j _ hij x hx => le_trans hx hij) ?_
    obtain ⟨r, h1, h2⟩ := (e3.and self_mem_nhdsWithin).exists
    exact ⟨r, h2, ne_top_of_le_ne_top
      (ENNReal.mul_ne_top hc' (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ωt)) h1.1⟩
  have th : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ d) * ω) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ d) * ω)) :=
    ENNReal.Tendsto.mul_const
      (((ENNReal.continuous_ofReal.comp (continuous_pow d)).tendsto 0).mono_left
        nhdsWithin_le_nhds) (Or.inr ωt)
  have z1 := le_of_tendsto_of_tendsto tg (ENNReal.Tendsto.const_mul (a := c) th (Or.inr hc'))
    (e3.mono fun r h => h.1)
  have z2 := le_of_tendsto_of_tendsto th (ENNReal.Tendsto.const_mul (a := c) tg (Or.inr hc'))
    (e3.mono fun r h => h.2)
  obtain ⟨δ, hδ, hs⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).1 e3
  have hδ' : (0 : ℝ) < δ := hδ
  have key : ∀ r, 0 ≤ r → r ≤ δ → μ {x | √(q x) ≤ r} ≤ c * (ENNReal.ofReal (r ^ d) * ω) ∧
      ENNReal.ofReal (r ^ d) * ω ≤ c * μ {x | √(q x) ≤ r} := by
    intro r h0 h1
    rcases h0.eq_or_lt with rfl | h0
    · exact ⟨z1, z2⟩
    · exact hs ⟨h0, h1⟩
  have key2 : ∀ t ≤ δ ^ 2,
      μ {x | q x ≤ t} ≤ c * volume {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ t} ∧
      volume {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ t} ≤ c * μ {x | q x ≤ t} := by
    intro t ht
    rcases lt_or_ge t 0 with h0 | h0
    · have a1 : {x | q x ≤ t} = ∅ := by
        ext x; simp; linarith [hq0 x]
      have a2 : {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ t} = ∅ := by
        ext x; simp; nlinarith [sq_nonneg ‖x‖]
      simp [a1, a2]
    · have := key (√t) (Real.sqrt_nonneg _) (Real.sqrt_le_iff.2 ⟨hδ'.le, ht⟩)
      rw [← volume_norm_sq_le d (Real.sqrt_nonneg _), setOf_sqrt_le q (Real.sqrt_nonneg _),
        Real.sq_sqrt h0] at this
      exact this
  exact ⟨δ ^ 2, by positivity, fun t ht => (key2 t ht).1, fun t ht => (key2 t ht).2⟩

theorem isRadial_of_sublevelLe {X : Type} [MeasurableSpace X] {μ : Measure X} {q : X → ℝ} {d : ℕ}
    (h : ∀ c : ℝ≥0∞, 1 < c → c ≠ ⊤ → ∃ T > 0,
      SublevelLe (c * c) T μ q volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) ∧
      SublevelLe (c * c) T volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) μ q) :
    IsRadial μ q d := by
  unfold IsRadial
  have hv := fun r => volume_norm_sq_le d (r := r)
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω
  have ev : ∀ T > (0 : ℝ), ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r ^ 2 ≤ T := by
    intro T hT
    filter_upwards [Ioc_mem_nhdsGT (Real.sqrt_pos.2 hT)] with r hr
    exact ⟨hr.1, (Real.le_sqrt hr.1.le hT.le).1 hr.2⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨c, c1, c2, c3⟩ := exists_one_lt_mul_mul_lt ha
    obtain ⟨T, hT, -, h2⟩ := h c c1 c2
    filter_upwards [ev T hT] with r ⟨hr, hrT⟩
    have n0 : ENNReal.ofReal (r ^ d) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have := h2 _ hrT
    rw [hv r hr.le, ← setOf_sqrt_le q hr.le, mul_comm,
      ← ENNReal.le_div_iff_mul_le (Or.inl n0) (Or.inl ENNReal.ofReal_ne_top),
      mul_div_assoc] at this
    by_contra hn
    have h3 : c * c * (μ {x | √(q x) ≤ r} / ENNReal.ofReal (r ^ d)) ≤ c * c * a := by
      gcongr; exact not_lt.1 hn
    exact absurd (c3.trans_le (this.trans h3)) (lt_irrefl _)
  · obtain ⟨c, c1, c2, c3⟩ := exists_one_lt_mul_mul_lt ha
    obtain ⟨T, hT, h1, -⟩ := h c c1 c2
    filter_upwards [ev T hT] with r ⟨hr, hrT⟩
    have n0 : ENNReal.ofReal (r ^ d) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have := h1 _ hrT
    rw [hv r hr.le, ← setOf_sqrt_le q hr.le] at this
    refine lt_of_le_of_lt ?_ c3
    rw [ENNReal.div_le_iff n0 ENNReal.ofReal_ne_top]
    calc _ ≤ _ := this
      _ = _ := by ring

theorem isRadial_prod : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (q : X → ℝ) (p : Y → ℝ) (d e : ℕ), Measurable q → Measurable p → (∀ x, 0 ≤ q x) → (∀ y, 0 ≤ p y) → IsRadial μ q d → IsRadial ν p e → IsRadial (μ.prod ν) (fun z => q z.1 + p z.2) (d + e) := by
  intro X Y _ _ μ ν _ _ q p d e hq hp hq0 hp0 h1 h2
  refine isRadial_of_sublevelLe fun c c1 c2 => ?_
  obtain ⟨T, hT, a1, a2⟩ := h1.sublevelLe hq hq0 c1 c2
  obtain ⟨T', hT', b1, b2⟩ := h2.sublevelLe hp hp0 c1 c2
  refine ⟨min T T', lt_min hT hT', fun t ht => ?_, fun t ht => ?_⟩
  · have := SublevelLe.prod c2 hq (by fun_prop) hp (by fun_prop) (fun _ => by positivity) hp0
      (a1.mono (min_le_left _ _)) (b1.mono (min_le_right _ _)) t ht
    rwa [volume_prod_norm_sq_le] at this
  · have := SublevelLe.prod c2 (by fun_prop) hq (by fun_prop) hp hq0 (fun _ => by positivity)
      (a2.mono (min_le_left _ _)) (b2.mono (min_le_right _ _)) t ht
    rwa [volume_prod_norm_sq_le] at this

end GlobalTheory.LeviIso
