import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.SmallBallProd

lemma cmp_zero {Y Y' : Type*} [MeasurableSpace Y] [MeasurableSpace Y'] (μ : Measure Y) (μ' : Measure Y')
    (ρ : Y → ℝ) (ρ' : Y' → ℝ) (hρ' : Measurable ρ') (a b : ENNReal) (hb : b ≠ ⊤) (r : ℝ) (hr : 0 < r)
    (hf : μ' {y | Real.sqrt (ρ' y) ≤ r} ≠ ⊤)
    (h : ∀ s, 0 < s → s ≤ r → a * μ {y | Real.sqrt (ρ y) ≤ s} ≤ b * μ' {y | Real.sqrt (ρ' y) ≤ s}) :
    ∀ s, 0 ≤ s → s ≤ r → a * μ {y | Real.sqrt (ρ y) ≤ s} ≤ b * μ' {y | Real.sqrt (ρ' y) ≤ s} := by
  intro s hs0 hsr
  rcases hs0.lt_or_eq with hs | hs
  · exact h s hs hsr
  subst hs

  let S : ℕ → Set Y' := fun n => {y | Real.sqrt (ρ' y) ≤ r / ((n : ℝ) + 1)}
  have hmeas : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_le (Real.continuous_sqrt.measurable.comp hρ') measurable_const
  have hanti : Antitone S := by
    intro m n hmn y hy
    have hle : r / ((n : ℝ) + 1) ≤ r / ((m : ℝ) + 1) :=
      div_le_div_of_nonneg_left hr.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    exact le_trans hy hle
  have hInter : (⋂ n, S n) = {y | Real.sqrt (ρ' y) ≤ 0} := by
    ext y
    simp only [S, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hy
      by_contra hne
      push_neg at hne
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hne hr)
      have hlt : r / ((n : ℝ) + 1) < Real.sqrt (ρ' y) := by
        calc r / ((n : ℝ) + 1) = r * (1 / ((n : ℝ) + 1)) := by ring
          _ < r * (Real.sqrt (ρ' y) / r) := mul_lt_mul_of_pos_left hn hr
          _ = Real.sqrt (ρ' y) := by field_simp
      linarith [hy n]
    · intro hy n
      exact hy.trans (div_nonneg hr.le (by positivity))
  have hfin : ∃ n, μ' (S n) ≠ ⊤ :=
    ⟨0, ne_top_of_le_ne_top hf (measure_mono fun y hy => by simpa [S] using hy)⟩
  have ht := tendsto_measure_iInter_atTop (fun n => (hmeas n).nullMeasurableSet) hanti hfin
  rw [hInter] at ht
  have ht2 := ENNReal.Tendsto.const_mul ht (Or.inr hb)
  refine ge_of_tendsto' ht2 (fun n => ?_)
  have hpos : 0 < r / ((n : ℝ) + 1) := div_pos hr (by positivity)
  have hsub : μ {y | Real.sqrt (ρ y) ≤ 0} ≤ μ {y | Real.sqrt (ρ y) ≤ r / ((n : ℝ) + 1)} :=
    measure_mono fun y (hy : Real.sqrt (ρ y) ≤ 0) => hy.trans hpos.le
  calc a * μ {y | Real.sqrt (ρ y) ≤ 0} ≤ a * μ {y | Real.sqrt (ρ y) ≤ r / ((n : ℝ) + 1)} := by
        gcongr
    _ ≤ b * μ' (S n) := h _ hpos (div_le_self hr.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]))

lemma section_eq {Y : Type*} (ρ : Y → ℝ) (c r : ℝ) (hr : 0 ≤ r) (hc : c ≤ r ^ 2) :
    {y | Real.sqrt (c + ρ y) ≤ r} = {y | Real.sqrt (ρ y) ≤ Real.sqrt (r ^ 2 - c)} := by
  have key : ∀ x : ℝ, Real.sqrt x ≤ r ↔ x ≤ r ^ 2 := fun x => by
    have := Real.sqrt_le_sqrt_iff (x := x) (y := r ^ 2) (by positivity)
    rwa [Real.sqrt_sq hr] at this
  ext y
  simp only [Set.mem_setOf_eq]
  rw [key, Real.sqrt_le_sqrt_iff (by linarith)]
  constructor <;> intro h <;> linarith

lemma section_empty {Y : Type*} (ρ : Y → ℝ) (h0 : ∀ y, 0 ≤ ρ y) (c r : ℝ) (hr : 0 ≤ r) (hc : r ^ 2 < c) :
    {y | Real.sqrt (c + ρ y) ≤ r} = ∅ := by
  have key : ∀ x : ℝ, Real.sqrt x ≤ r ↔ x ≤ r ^ 2 := fun x => by
    have := Real.sqrt_le_sqrt_iff (x := x) (y := r ^ 2) (by positivity)
    rwa [Real.sqrt_sq hr] at this
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hy
  rw [key] at hy
  linarith [h0 y]

lemma cmp_right {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Y']
    (ν : Measure X) (μ : Measure Y) (μ' : Measure Y') [SFinite μ] [SFinite μ']
    (σ : X → ℝ) (ρ : Y → ℝ) (ρ' : Y' → ℝ) (hσ : Measurable σ) (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (σ0 : ∀ x, 0 ≤ σ x) (ρ0 : ∀ y, 0 ≤ ρ y) (a b : ENNReal) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ s, 0 ≤ s → s ≤ r → a * μ {y | Real.sqrt (ρ y) ≤ s} ≤ b * μ' {y | Real.sqrt (ρ' y) ≤ s}) :
    a * (ν.prod μ) {x | Real.sqrt (σ x.1 + ρ x.2) ≤ r}
      ≤ b * (ν.prod μ') {x | Real.sqrt (σ x.1 + ρ' x.2) ≤ r} := by
  have hS : MeasurableSet {x : X × Y | Real.sqrt (σ x.1 + ρ x.2) ≤ r} :=
    measurableSet_le (Real.continuous_sqrt.measurable.comp
      ((hσ.comp measurable_fst).add (hρ.comp measurable_snd))) measurable_const
  have hS' : MeasurableSet {x : X × Y' | Real.sqrt (σ x.1 + ρ' x.2) ≤ r} :=
    measurableSet_le (Real.continuous_sqrt.measurable.comp
      ((hσ.comp measurable_fst).add (hρ'.comp measurable_snd))) measurable_const

  have hpt : ∀ x, a * μ {y | Real.sqrt (σ x + ρ y) ≤ r} ≤ b * μ' {y | Real.sqrt (σ x + ρ' y) ≤ r} := by
    intro x
    by_cases hx : σ x ≤ r ^ 2
    · rw [section_eq ρ (σ x) r hr hx, section_eq ρ' (σ x) r hr hx]
      refine h _ (Real.sqrt_nonneg _) ?_
      calc Real.sqrt (r ^ 2 - σ x) ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt (by linarith [σ0 x])
        _ = r := Real.sqrt_sq hr
    · push_neg at hx
      rw [section_empty ρ ρ0 (σ x) r hr hx]
      simp
  rw [Measure.prod_apply hS, Measure.prod_apply hS']
  calc a * ∫⁻ x, μ (Prod.mk x ⁻¹' {p : X × Y | Real.sqrt (σ p.1 + ρ p.2) ≤ r}) ∂ν
      ≤ ∫⁻ x, a * μ (Prod.mk x ⁻¹' {p : X × Y | Real.sqrt (σ p.1 + ρ p.2) ≤ r}) ∂ν :=
        lintegral_const_mul_le _ _
    _ ≤ ∫⁻ x, b * μ' (Prod.mk x ⁻¹' {p : X × Y' | Real.sqrt (σ p.1 + ρ' p.2) ≤ r}) ∂ν :=
        lintegral_mono fun x => hpt x
    _ = b * ∫⁻ x, μ' (Prod.mk x ⁻¹' {p : X × Y' | Real.sqrt (σ p.1 + ρ' p.2) ≤ r}) ∂ν :=
        lintegral_const_mul b (measurable_measure_prodMk_left hS')

lemma prod_swap_level {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (μ : Measure Y) [SFinite ν] [SFinite μ]
    (σ : X → ℝ) (ρ : Y → ℝ) (hσ : Measurable σ) (hρ : Measurable ρ) (r : ℝ) :
    (ν.prod μ) {x | Real.sqrt (σ x.1 + ρ x.2) ≤ r}
      = (μ.prod ν) {x | Real.sqrt (ρ x.1 + σ x.2) ≤ r} := by
  have hS : MeasurableSet {x : X × Y | Real.sqrt (σ x.1 + ρ x.2) ≤ r} :=
    measurableSet_le (Real.continuous_sqrt.measurable.comp
      ((hσ.comp measurable_fst).add (hρ.comp measurable_snd))) measurable_const
  rw [← Measure.prod_swap (μ := μ) (ν := ν), Measure.map_apply measurable_swap hS]
  congr 1
  ext p
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Prod.fst_swap, Prod.snd_swap]
  rw [add_comm]

lemma cmp_both {X X' Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
    [MeasurableSpace Y']
    (ν : Measure X) (ν' : Measure X') (μ : Measure Y) (μ' : Measure Y') [SFinite ν] [SFinite ν']
    [SFinite μ] [SFinite μ']
    (σ : X → ℝ) (σ' : X' → ℝ) (ρ : Y → ℝ) (ρ' : Y' → ℝ) (hσ : Measurable σ) (hσ' : Measurable σ')
    (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (σ0 : ∀ x, 0 ≤ σ x) (ρ0 : ∀ y, 0 ≤ ρ y) (ρ0' : ∀ y, 0 ≤ ρ' y)
    (a b a' b' : ENNReal) (r : ℝ) (hr : 0 ≤ r)
    (h1 : ∀ s, 0 ≤ s → s ≤ r → a' * ν {y | Real.sqrt (σ y) ≤ s} ≤ b' * ν' {y | Real.sqrt (σ' y) ≤ s})
    (h2 : ∀ s, 0 ≤ s → s ≤ r → a * μ {y | Real.sqrt (ρ y) ≤ s} ≤ b * μ' {y | Real.sqrt (ρ' y) ≤ s}) :
    a' * a * (ν.prod μ) {x | Real.sqrt (σ x.1 + ρ x.2) ≤ r}
      ≤ b' * b * (ν'.prod μ') {x | Real.sqrt (σ' x.1 + ρ' x.2) ≤ r} := by
  have e1 := cmp_right ν μ μ' σ ρ ρ' hσ hρ hρ' σ0 ρ0 a b r hr h2
  have e2 := cmp_right μ' ν ν' ρ' σ σ' hρ' hσ hσ' ρ0' σ0 a' b' r hr h1
  calc a' * a * (ν.prod μ) {x | Real.sqrt (σ x.1 + ρ x.2) ≤ r}
      = a' * (a * (ν.prod μ) {x | Real.sqrt (σ x.1 + ρ x.2) ≤ r}) := by ring
    _ ≤ a' * (b * (ν.prod μ') {x | Real.sqrt (σ x.1 + ρ' x.2) ≤ r}) := by gcongr a' * ?_
    _ = b * (a' * (μ'.prod ν) {x | Real.sqrt (ρ' x.1 + σ x.2) ≤ r}) := by
        rw [prod_swap_level ν μ' σ ρ' hσ hρ' r]; ring
    _ ≤ b * (b' * (μ'.prod ν') {x | Real.sqrt (ρ' x.1 + σ' x.2) ≤ r}) := by gcongr b * ?_
    _ = b' * b * (ν'.prod μ') {x | Real.sqrt (σ' x.1 + ρ' x.2) ≤ r} := by
        rw [prod_swap_level ν' μ' σ' ρ' hσ' hρ' r]; ring

lemma vol_level (d : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (volume : Measure (EuclideanSpace ℝ (Fin d))) {y | Real.sqrt (‖y‖ ^ 2) ≤ s}
      = ENNReal.ofReal (s ^ d) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  have hset : {y : EuclideanSpace ℝ (Fin d) | Real.sqrt (‖y‖ ^ 2) ≤ s} = Metric.closedBall 0 s := by
    ext y
    simp [Real.sqrt_sq (norm_nonneg _)]
  rw [hset, Measure.addHaar_closedBall volume 0 hs, finrank_euclideanSpace_fin]

lemma vol_prod_level (d e : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod (volume : Measure (EuclideanSpace ℝ (Fin e))))
        {y | Real.sqrt (‖y.1‖ ^ 2 + ‖y.2‖ ^ 2) ≤ s}
      = ENNReal.ofReal (s ^ (d + e)) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d + e))) 1) := by

  let Φ : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e) → EuclideanSpace ℝ (Fin (d + e)) :=
    fun y => WithLp.toLp 2 (MeasurableEquiv.piCongrLeft (fun _ : Fin (d + e) => ℝ) finSumFinEquiv
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin d ⊕ Fin e => ℝ)).symm
        (WithLp.ofLp y.1, WithLp.ofLp y.2)))
  have hΦ : MeasurePreserving Φ
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod (volume : Measure (EuclideanSpace ℝ (Fin e))))
      volume := by
    have h1 := (PiLp.volume_preserving_ofLp (Fin d)).prod (PiLp.volume_preserving_ofLp (Fin e))
    have h2 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin d ⊕ Fin e => ℝ)
    have h3 := volume_measurePreserving_piCongrLeft (fun _ : Fin (d + e) => ℝ) finSumFinEquiv
    have h4 := PiLp.volume_preserving_toLp (Fin (d + e))
    exact h4.comp (h3.comp (h2.comp h1))
  have hnorm : ∀ y, ‖Φ y‖ ^ 2 = ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
    intro y
    have hL : ∀ i : Fin d, (Φ y).ofLp (finSumFinEquiv (Sum.inl i)) = y.1.ofLp i := fun i => by
      show (Equiv.piCongrLeft (fun _ : Fin (d + e) => ℝ) finSumFinEquiv
          ((Equiv.sumPiEquivProdPi (fun _ : Fin d ⊕ Fin e => ℝ)).symm (y.1.ofLp, y.2.ofLp)))
          (finSumFinEquiv (Sum.inl i)) = y.1.ofLp i
      rw [Equiv.piCongrLeft_apply_apply]
      rfl
    have hR : ∀ j : Fin e, (Φ y).ofLp (finSumFinEquiv (Sum.inr j)) = y.2.ofLp j := fun j => by
      show (Equiv.piCongrLeft (fun _ : Fin (d + e) => ℝ) finSumFinEquiv
          ((Equiv.sumPiEquivProdPi (fun _ : Fin d ⊕ Fin e => ℝ)).symm (y.1.ofLp, y.2.ofLp)))
          (finSumFinEquiv (Sum.inr j)) = y.2.ofLp j
      rw [Equiv.piCongrLeft_apply_apply]
      rfl
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
      ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    simp only [hL, hR]
  have hT : MeasurableSet {z : EuclideanSpace ℝ (Fin (d + e)) | Real.sqrt (‖z‖ ^ 2) ≤ s} :=
    measurableSet_le (Real.continuous_sqrt.measurable.comp (continuous_norm.pow 2).measurable)
      measurable_const
  have hpre : Φ ⁻¹' {z : EuclideanSpace ℝ (Fin (d + e)) | Real.sqrt (‖z‖ ^ 2) ≤ s}
      = {y | Real.sqrt (‖y.1‖ ^ 2 + ‖y.2‖ ^ 2) ≤ s} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hnorm]
  rw [← hpre, hΦ.measure_preimage hT.nullMeasurableSet, vol_level (d + e) s hs]

lemma tendsto_of_two_sided {f : ℝ → ENNReal} {l : Filter ℝ} {L : ENNReal}
    (h : ∀ t : ENNReal, 1 < t → t ≠ ⊤ → ∀ᶠ r in l, f r ≤ t * t * L ∧ L ≤ t * t * f r) :
    Filter.Tendsto f l (nhds L) := by
  let t : ℕ → ENNReal := fun n => 1 + ((n + 1 : ℕ) : ENNReal)⁻¹
  have ht1 : ∀ n, 1 < t n := fun n =>
    ENNReal.lt_add_right ENNReal.one_ne_top (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
  have httop : ∀ n, t n ≠ ⊤ := fun n =>
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.2 (by exact_mod_cast Nat.succ_ne_zero n)⟩
  have htl : Filter.Tendsto t Filter.atTop (nhds 1) := by
    have h0 : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ENNReal)⁻¹) Filter.atTop (nhds 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
    have := (tendsto_const_nhds (x := (1 : ENNReal))).add h0
    rw [add_zero] at this
    exact this
  have hsq : ∀ c : ENNReal, c ≠ ⊤ → Filter.Tendsto (fun n => t n * t n * c) Filter.atTop (nhds c) := by
    intro c hc
    have := ENNReal.Tendsto.mul_const (ENNReal.Tendsto.mul htl (Or.inl one_ne_zero) htl (Or.inl one_ne_zero)) (Or.inr hc)
    rw [one_mul, one_mul] at this
    exact this
  rw [tendsto_order]
  constructor
  · intro l hl
    obtain ⟨n, hn⟩ := ((hsq l (ne_top_of_lt hl)).eventually (gt_mem_nhds hl)).exists
    filter_upwards [h (t n) (ht1 n) (httop n)] with x hx
    by_contra hc
    push_neg at hc
    have : t n * t n * f x ≤ t n * t n * l := by gcongr
    exact absurd (hn.trans_le (hx.2.trans this)) (lt_irrefl _)
  · intro u hu
    obtain ⟨n, hn⟩ := ((hsq L (ne_top_of_lt hu)).eventually (gt_mem_nhds hu)).exists
    filter_upwards [h (t n) (ht1 n) (httop n)] with x hx
    exact hx.1.trans_lt hn

lemma two_sided_of_tendsto {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (d : ℕ) (C : ℝ) (hC : 0 < C)
    (h : Filter.Tendsto (fun r : ℝ => ν {x | Real.sqrt (ρ x) ≤ r} / ENNReal.ofReal (r ^ d))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ENNReal.ofReal C * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))))
    (t : ENNReal) (ht : 1 < t) (ht' : t ≠ ⊤) :
    ∃ r0 > 0, (∀ s, 0 ≤ s → s ≤ r0 → 1 * ν {x | Real.sqrt (ρ x) ≤ s} ≤ (t * ENNReal.ofReal C) *
        (volume : Measure (EuclideanSpace ℝ (Fin d))) {y | Real.sqrt (‖y‖ ^ 2) ≤ s}) ∧
      (∀ s, 0 ≤ s → s ≤ r0 → ENNReal.ofReal C *
        (volume : Measure (EuclideanSpace ℝ (Fin d))) {y | Real.sqrt (‖y‖ ^ 2) ≤ s}
          ≤ t * ν {x | Real.sqrt (ρ x) ≤ s}) := by
  set V := (volume : Measure (EuclideanSpace ℝ (Fin d))) (Metric.ball 0 1) with hVdef
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos _ _ one_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  set K := ENNReal.ofReal C * V with hKdef
  have hK0 : K ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.2 hC).ne' hV0
  have hKt : K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have hup : K < t * K := by simpa using ENNReal.mul_lt_mul_left hK0 hKt ht
  have hKK : K < K * t := by rw [mul_comm]; exact hup
  have hlow : K / t < K := ENNReal.div_lt_of_lt_mul hKK
  have e1 := h.eventually (gt_mem_nhds hup)
  have e2 := h.eventually (lt_mem_nhds hlow)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (e1.and e2)
  have hu0 : (0 : ℝ) < u := hu
  have hX : ∀ s : ℝ, 0 < s → ENNReal.ofReal (s ^ d) ≠ 0 ∧ ENNReal.ofReal (s ^ d) ≠ ⊤ := fun s hs =>
    ⟨(ENNReal.ofReal_pos.2 (pow_pos hs d)).ne', ENNReal.ofReal_ne_top⟩
  have hvol : ∀ s : ℝ, 0 ≤ s → (volume : Measure (EuclideanSpace ℝ (Fin d)))
      {y | Real.sqrt (‖y‖ ^ 2) ≤ s} = ENNReal.ofReal (s ^ d) * V := fun s hs => vol_level d s hs
  have hm : Measurable (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖ ^ 2) := (continuous_norm.pow 2).measurable
  refine ⟨u / 2, by positivity, ?_, ?_⟩
  · refine cmp_zero ν volume ρ (fun y => ‖y‖ ^ 2) hm 1 (t * ENNReal.ofReal C)
      (ENNReal.mul_ne_top ht' ENNReal.ofReal_ne_top) (u / 2) (by positivity) ?_ ?_
    · show (volume : Measure (EuclideanSpace ℝ (Fin d))) {y | Real.sqrt (‖y‖ ^ 2) ≤ u / 2} ≠ ⊤
      rw [hvol _ (by positivity)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt
    · intro s hs hsu
      have hs' : s ∈ Set.Ioo 0 u := ⟨hs, by linarith⟩
      obtain ⟨h1, -⟩ := hsub hs'
      have h1' : ν {x | Real.sqrt (ρ x) ≤ s} / ENNReal.ofReal (s ^ d) ≤ t * K := h1.le
      show 1 * ν {x | Real.sqrt (ρ x) ≤ s}
        ≤ t * ENNReal.ofReal C * (volume : Measure (EuclideanSpace ℝ (Fin d))) {y | Real.sqrt (‖y‖ ^ 2) ≤ s}
      rw [hvol s hs.le]
      obtain ⟨hX0, hXt⟩ := hX s hs
      calc 1 * ν {x | Real.sqrt (ρ x) ≤ s}
          = ν {x | Real.sqrt (ρ x) ≤ s} / ENNReal.ofReal (s ^ d) * ENNReal.ofReal (s ^ d) := by
            rw [one_mul, ENNReal.div_mul_cancel hX0 hXt]
        _ ≤ t * K * ENNReal.ofReal (s ^ d) := by gcongr
        _ = t * ENNReal.ofReal C * (ENNReal.ofReal (s ^ d) * V) := by rw [hKdef]; ring
  · refine cmp_zero volume ν (fun y => ‖y‖ ^ 2) ρ hρ (ENNReal.ofReal C) t ht' (u / 2) (by positivity)
      (measure_ne_top ν _) ?_
    intro s hs hsu
    have hs' : s ∈ Set.Ioo 0 u := ⟨hs, by linarith⟩
    obtain ⟨-, h2⟩ := hsub hs'
    have h2' : K < ν {x | Real.sqrt (ρ x) ≤ s} / ENNReal.ofReal (s ^ d) * t :=
      (ENNReal.div_lt_iff (Or.inl ht0) (Or.inl ht')).1 h2
    have h2'' := h2'.le
    show ENNReal.ofReal C * (volume : Measure (EuclideanSpace ℝ (Fin d))) {y | Real.sqrt (‖y‖ ^ 2) ≤ s}
      ≤ t * ν {x | Real.sqrt (ρ x) ≤ s}
    rw [hvol s hs.le]
    obtain ⟨hX0, hXt⟩ := hX s hs
    calc ENNReal.ofReal C * (ENNReal.ofReal (s ^ d) * V) = K * ENNReal.ofReal (s ^ d) := by
          rw [hKdef]; ring
      _ ≤ ν {x | Real.sqrt (ρ x) ≤ s} / ENNReal.ofReal (s ^ d) * t * ENNReal.ofReal (s ^ d) := by
          gcongr
      _ = t * ν {x | Real.sqrt (ρ x) ≤ s} := by
          rw [mul_comm _ t, mul_assoc, ENNReal.div_mul_cancel hX0 hXt]

theorem tendsto_prod_smallBall : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (ν₁ : Measure X) (ν₂ : Measure Y) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] (ρ₁ : X → ℝ) (ρ₂ : Y → ℝ) (d₁ d₂ : ℕ) (C₁ C₂ : ℝ), Measurable ρ₁ → Measurable ρ₂ → (∀ x, 0 ≤ ρ₁ x) → (∀ y, 0 ≤ ρ₂ y) → 0 < C₁ → 0 < C₂ → Filter.Tendsto (fun r : ℝ => ν₁ {x | Real.sqrt (ρ₁ x) ≤ r} / ENNReal.ofReal (r ^ (d₁))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (C₁) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₁))) 1))) → Filter.Tendsto (fun r : ℝ => ν₂ {x | Real.sqrt (ρ₂ x) ≤ r} / ENNReal.ofReal (r ^ (d₂))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (C₂) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₂))) 1))) → Filter.Tendsto (fun r : ℝ => (ν₁.prod ν₂) {x | Real.sqrt (ρ₁ x.1 + ρ₂ x.2) ≤ r} / ENNReal.ofReal (r ^ (d₁ + d₂))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (C₁ * C₂) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₁ + d₂))) 1))) := by
  intro X Y _ _ ν₁ ν₂ _ _ ρ₁ ρ₂ d₁ d₂ C₁ C₂ hρ₁ hρ₂ h0₁ h0₂ hC₁ hC₂ h₁ h₂
  apply tendsto_of_two_sided
  intro t ht ht'
  obtain ⟨r₁, hr₁, u₁, l₁⟩ := two_sided_of_tendsto ν₁ ρ₁ hρ₁ d₁ C₁ hC₁ h₁ t ht ht'
  obtain ⟨r₂, hr₂, u₂, l₂⟩ := two_sided_of_tendsto ν₂ ρ₂ hρ₂ d₂ C₂ hC₂ h₂ t ht ht'
  have hm₁ : Measurable (fun y : EuclideanSpace ℝ (Fin d₁) => ‖y‖ ^ 2) :=
    (continuous_norm.pow 2).measurable
  have hm₂ : Measurable (fun y : EuclideanSpace ℝ (Fin d₂) => ‖y‖ ^ 2) :=
    (continuous_norm.pow 2).measurable
  filter_upwards [Ioo_mem_nhdsGT (lt_min hr₁ hr₂)] with r hr
  have hr0 : 0 ≤ r := hr.1.le
  have hr1 : r ≤ r₁ := hr.2.le.trans (min_le_left _ _)
  have hr2 : r ≤ r₂ := hr.2.le.trans (min_le_right _ _)
  have hup := cmp_both ν₁ volume ν₂ volume ρ₁ (fun y => ‖y‖ ^ 2) ρ₂ (fun y => ‖y‖ ^ 2)
    hρ₁ hm₁ hρ₂ hm₂ h0₁ h0₂ (fun y => sq_nonneg _) 1 (t * ENNReal.ofReal C₂) 1
    (t * ENNReal.ofReal C₁) r hr0
    (fun s hs hsr => u₁ s hs (hsr.trans hr1)) (fun s hs hsr => u₂ s hs (hsr.trans hr2))
  have hlow := cmp_both volume ν₁ volume ν₂ (fun y => ‖y‖ ^ 2) ρ₁ (fun y => ‖y‖ ^ 2) ρ₂
    hm₁ hρ₁ hm₂ hρ₂ (fun y => sq_nonneg _) (fun y => sq_nonneg _) h0₂ (ENNReal.ofReal C₂) t
    (ENNReal.ofReal C₁) t r hr0
    (fun s hs hsr => l₁ s hs (hsr.trans hr1)) (fun s hs hsr => l₂ s hs (hsr.trans hr2))
  beta_reduce at hup hlow
  rw [vol_prod_level d₁ d₂ r hr0] at hup hlow
  have hX0 : ENNReal.ofReal (r ^ (d₁ + d₂)) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hr.1 _)).ne'
  have hXt : ENNReal.ofReal (r ^ (d₁ + d₂)) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.ofReal_mul hC₁.le]
  constructor
  · apply ENNReal.div_le_of_le_mul
    calc (ν₁.prod ν₂) {x | Real.sqrt (ρ₁ x.1 + ρ₂ x.2) ≤ r}
        = 1 * 1 * (ν₁.prod ν₂) {x | Real.sqrt (ρ₁ x.1 + ρ₂ x.2) ≤ r} := by ring
      _ ≤ t * ENNReal.ofReal C₁ * (t * ENNReal.ofReal C₂) * (ENNReal.ofReal (r ^ (d₁ + d₂)) *
            volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₁ + d₂))) 1)) := hup
      _ = t * t * (ENNReal.ofReal C₁ * ENNReal.ofReal C₂ *
            volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₁ + d₂))) 1)) *
            ENNReal.ofReal (r ^ (d₁ + d₂)) := by ring
  · rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hX0) (Or.inl hXt)]
    calc ENNReal.ofReal C₁ * ENNReal.ofReal C₂ *
            volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₁ + d₂))) 1) *
            ENNReal.ofReal (r ^ (d₁ + d₂))
        = ENNReal.ofReal C₁ * ENNReal.ofReal C₂ * (ENNReal.ofReal (r ^ (d₁ + d₂)) *
            volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₁ + d₂))) 1)) := by ring
      _ ≤ t * t * (ν₁.prod ν₂) {x | Real.sqrt (ρ₁ x.1 + ρ₂ x.2) ≤ r} := hlow

end GlobalTheory.SmallBallProd
