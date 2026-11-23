import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionImageSup
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartSup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Set Filter Topology

noncomputable section

namespace BlockResolutionImageSup

theorem analyticOnNhd_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {σ : Type*} {V : Set E}
    {g : E → σ → ℂ} (hg : ∀ i, AnalyticOnNhd ℂ (fun w => g w i) V) (f : MvPolynomial σ ℂ) :
    AnalyticOnNhd ℂ (fun w => eval (g w) f) V := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : E => a) V)
  | add p q hp hq => exact fun w hw => by simpa using (hp w hw).fun_add (hq w hw)
  | mul_X p i hp => exact fun w hw => by simpa using (hp w hw).fun_mul (hg i w hw)

theorem sq_div_pow_eq {a r : ℝ} (hr : 0 < r) (n : ℕ) :
    (a / r ^ n) ^ 2 = a ^ 2 * Real.exp (-(n : ℝ) * (2 * Real.log r)) := by
  have h : Real.exp (-(n : ℝ) * (2 * Real.log r)) = ((r ^ n) ^ 2)⁻¹ := by
    rw [show -(n : ℝ) * (2 * Real.log r) = -Real.log ((r ^ n) ^ 2) by
      rw [Real.log_pow, Real.log_pow]; push_cast; ring, Real.exp_neg, Real.exp_log (by positivity)]
  rw [h, div_pow, div_eq_mul_inv]

theorem lintegral_chart_le {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {e : ℕ}
    (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (μ : Measure X) {ν : (Fin e → ℂ) → ℝ}
    (hν : ContinuousOn ν φ.target)
    (hμ : ∀ S : Set X, MeasurableSet S → S ⊆ φ.source →
      μ S = ∫⁻ y in φ.target ∩ φ.symm ⁻¹' S, ENNReal.ofReal (ν y))
    {g : X → ENNReal} (hg : Measurable g) :
    ∫⁻ z in φ.target, ENNReal.ofReal (ν z) * g (φ.symm z) ≤ ∫⁻ y, g y ∂μ := by
  have hT : MeasurableSet φ.target := φ.open_target.measurableSet
  have hs : AEMeasurable φ.symm (volume.restrict φ.target) := φ.continuousOn_symm.aemeasurable hT
  have hνm : AEMeasurable (fun z => ENNReal.ofReal (ν z)) (volume.restrict φ.target) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hν.aemeasurable hT)
  have hs' : AEMeasurable φ.symm
      ((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z)) :=
    hs.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmap : Measure.map φ.symm ((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z)) =
      μ.restrict φ.source := by
    ext S hS
    have hset : φ.symm ⁻¹' S ∩ φ.target = φ.target ∩ φ.symm ⁻¹' (S ∩ φ.source) := by
      ext z
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, φ.map_target h2⟩
      · rintro ⟨h2, h1, -⟩
        exact ⟨h1, h2⟩
    rw [Measure.map_apply_of_aemeasurable hs' hS, withDensity_apply' _ _, Measure.restrict_restrict' hT,
      Measure.restrict_apply hS, hμ _ (hS.inter φ.open_source.measurableSet) inter_subset_right, hset]
  calc ∫⁻ z in φ.target, ENNReal.ofReal (ν z) * g (φ.symm z)
      = ∫⁻ z, g (φ.symm z) ∂((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z)) :=
        (lintegral_withDensity_eq_lintegral_mul₀ hνm (hg.comp_aemeasurable hs)).symm
    _ = ∫⁻ y, g y ∂(Measure.map φ.symm
          ((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z))) :=
        (lintegral_map' hg.aemeasurable hs').symm
    _ = ∫⁻ y in φ.source, g y ∂μ := by rw [hmap]
    _ ≤ ∫⁻ y, g y ∂μ := setLIntegral_le_lintegral _ _

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem eval_torus {f : MRingOver ℂ ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) f = c k₀ ^ n * eval z f := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hf m hm
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = c k₀ ^ n := by
    rw [Fintype.prod_sigma]
    simp_rw [Finset.prod_pow_eq_pow_sum, hdeg]
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [blockDeg, hk]]
    simp [blockDeg]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem normRatio_torus {f : MRingOver ℂ ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    (A : HermLine ι) (hA : A.a = unitDeg k₀) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ‖eval z f‖ / A.h z ^ n = ‖eval z' f‖ / A.h z' ^ n := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [eval_torus hf, A.smul c z' hc, hA]
  have hprod : ∏ k, ‖c k‖ ^ unitDeg k₀ k = ‖c k₀‖ := by
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [unitDeg, hk]]
    simp [unitDeg]
  rw [hprod, norm_mul, norm_pow, mul_pow]
  have : ‖c k₀‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hc k₀))
  rw [mul_div_mul_left _ _ this]

theorem lift_blockNonzero (d : HSMBlockDatum D K ι Ω) {x y : d.R.X} (hy : y ∈ d.R.U x) :
    ∀ k, ∃ i, d.R.lift x y ⟨k, i⟩ ≠ 0 :=
  (d.R.mem x y hy).1

theorem ratio_blockPt_eq (d : HSMBlockDatum D K ι Ω) {n : ℕ} {f : MRingOver ℂ ι}
    (hf : IsMultiHomog f (blockDeg d.k₀ n)) {x y : d.R.X} (hy : y ∈ d.R.U x) :
    ‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n =
      ‖eval (d.R.lift x y) f‖ / d.A.h (d.R.lift x y) ^ n :=
  normRatio_torus hf d.A d.deg (d.R.compat y x y ⟨d.R.mem_U y, hy⟩)

theorem continuous_ratio (d : HSMBlockDatum D K ι Ω) {n : ℕ} {f : MRingOver ℂ ι}
    (hf : IsMultiHomog f (blockDeg d.k₀ n)) :
    Continuous fun y => ‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n := by
  rw [continuous_iff_continuousAt]
  intro y₀
  obtain ⟨j, hj⟩ := d.R.A.cover y₀
  set e := d.R.A.chart j with he
  have hL : ContinuousAt (d.R.lift y₀) y₀ := by
    rw [continuousAt_pi]
    intro p
    have ha : AnalyticAt ℂ ((fun y => d.R.lift y₀ y p) ∘ e.symm) (e y₀) :=
      d.R.holo y₀ p j (e y₀) ⟨e.map_source hj, by rw [mem_preimage, e.left_inv hj]; exact d.R.mem_U y₀⟩
    refine (ha.continuousAt.comp (e.continuousAt hj)).congr ?_
    filter_upwards [e.open_source.mem_nhds hj] with y hy
    simp only [Function.comp_apply, e.left_inv hy]
  have hne := lift_blockNonzero d (d.R.mem_U y₀)
  have hh : ContinuousAt d.A.h (d.R.lift y₀ y₀) :=
    d.semipos.1.continuousOn.continuousAt (isOpen_blockNonzero.mem_nhds hne)
  have hcont : ContinuousAt (fun y => ‖eval (d.R.lift y₀ y) f‖ / d.A.h (d.R.lift y₀ y) ^ n) y₀ :=
    (((MvPolynomial.continuous_eval f).continuousAt.comp hL).norm).div ((hh.comp hL).pow n)
      (pow_pos (d.A.pos _ hne) n).ne'
  refine hcont.congr ?_
  filter_upwards [(d.R.isOpen_U y₀).mem_nhds (d.R.mem_U y₀)] with y hy
  exact (ratio_blockPt_eq d hf hy).symm

theorem local_bound (hC : ChartSupBound.Statement) (d : HSMBlockDatum D K ι Ω) (x₀ : d.R.X) :
    ∃ N : Set d.R.X, IsOpen N ∧ x₀ ∈ N ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ f : MRingOver ℂ ι, IsMultiHomog f (blockDeg d.k₀ n) → ∀ y ∈ N,
        (‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2 ≤
          C * (n : ℝ) ^ D * blockL2NormComplex d n f ^ 2 := by
  have : IsProbabilityMeasure d.dV := d.vol.1
  obtain ⟨j, hj⟩ := d.R.A.cover x₀
  set e := d.R.A.chart j with he
  obtain ⟨ν, hνs, hνpos, hνV⟩ := d.vol.2 j
  have hVo : IsOpen (e.target ∩ e.symm ⁻¹' d.R.U x₀) := e.isOpen_inter_preimage_symm (d.R.isOpen_U x₀)
  have hx₀V : e x₀ ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀ :=
    ⟨e.map_source hj, by rw [mem_preimage, e.left_inv hj]; exact d.R.mem_U x₀⟩
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.1 hVo _ hx₀V
  have hKV : Metric.closedBall (e x₀) (δ / 2) ⊆ e.target ∩ e.symm ⁻¹' d.R.U x₀ :=
    (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hδV
  have hLa : ∀ p, AnalyticOnNhd ℂ (fun w => d.R.lift x₀ (e.symm w) p) (e.target ∩ e.symm ⁻¹' d.R.U x₀) :=
    fun p => d.R.holo x₀ p j
  have hLne : ∀ w ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀, ∀ k, ∃ i, d.R.lift x₀ (e.symm w) ⟨k, i⟩ ≠ 0 :=
    fun w hw => lift_blockNonzero d hw.2
  have hψ : ContDiffOn ℝ 2 (fun w => 2 * Real.log (d.A.h (d.R.lift x₀ (e.symm w))))
      (e.target ∩ e.symm ⁻¹' d.R.U x₀) := by
    have hL2 : ContDiffOn ℝ 2 (fun w => d.R.lift x₀ (e.symm w)) (e.target ∩ e.symm ⁻¹' d.R.U x₀) :=
      contDiffOn_pi.2 fun p => ((hLa p).contDiffOn_of_completeSpace).restrict_scalars ℝ
    have hh : ContDiffOn ℝ 2 (fun w => d.A.h (d.R.lift x₀ (e.symm w))) (e.target ∩ e.symm ⁻¹' d.R.U x₀) :=
      (d.semipos.1.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).comp hL2 fun w hw => hLne w hw
    exact contDiffOn_const.mul (hh.log fun w hw => (d.A.pos _ (hLne w hw)).ne')
  obtain ⟨C₀, hC₀⟩ := hC D (e.target ∩ e.symm ⁻¹' d.R.U x₀) (Metric.closedBall (e x₀) (δ / 2)) _ ν hVo
    (isCompact_closedBall _ _) hKV hψ (hνs.continuousOn.mono inter_subset_left) fun z hz => hνpos z hz.1
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e x₀) (δ / 2), e.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨hj, Metric.mem_ball_self (half_pos hδ)⟩, max C₀ 0, le_max_right _ _, fun n hn f hf y hy => ?_⟩
  have hgc := (continuous_ratio d hf).pow 2
  have hgm : Measurable fun y => ENNReal.ofReal ((‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2) :=
    ENNReal.measurable_ofReal.comp hgc.measurable
  have hgi : Integrable (fun y => (‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2) d.dV :=
    hgc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI0 : 0 ≤ ∫ y, (‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2 ∂d.dV :=
    integral_nonneg fun y => sq_nonneg _
  have hres : blockL2NormComplex d n f ^ 2 = ∫ y, (‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2 ∂d.dV := by
    rw [blockL2NormComplex, Real.sq_sqrt hI0]
  have hid : ∀ w ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀,
      ‖eval (d.R.lift x₀ (e.symm w)) f‖ ^ 2 *
          Real.exp (-(n : ℝ) * (2 * Real.log (d.A.h (d.R.lift x₀ (e.symm w))))) =
        (‖eval (blockPt d (e.symm w)) f‖ / d.A.h (blockPt d (e.symm w)) ^ n) ^ 2 := by
    intro w hw
    rw [ratio_blockPt_eq d hf hw.2]
    exact (sq_div_pow_eq (d.A.pos _ (hLne w hw)) n).symm
  have key := hC₀ n hn _ (analyticOnNhd_eval hLa f) (e y) (Metric.ball_subset_closedBall hy.2)
  have hyV : e y ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀ := hKV (Metric.ball_subset_closedBall hy.2)
  rw [hid _ hyV, e.left_inv hy.1] at key
  have hint : ∫⁻ z in e.target ∩ e.symm ⁻¹' d.R.U x₀,
      ENNReal.ofReal (‖eval (d.R.lift x₀ (e.symm z)) f‖ ^ 2 *
        Real.exp (-(n : ℝ) * (2 * Real.log (d.A.h (d.R.lift x₀ (e.symm z))))) * ν z) ≤
      ENNReal.ofReal (blockL2NormComplex d n f ^ 2) := by
    rw [hres, ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun y => sq_nonneg _)]
    calc _ = ∫⁻ z in e.target ∩ e.symm ⁻¹' d.R.U x₀, ENNReal.ofReal (ν z) *
            ENNReal.ofReal ((‖eval (blockPt d (e.symm z)) f‖ / d.A.h (blockPt d (e.symm z)) ^ n) ^ 2) := by
          refine setLIntegral_congr_fun hVo.measurableSet fun z hz => ?_
          rw [hid z hz, mul_comm, ENNReal.ofReal_mul (hνpos z hz.1).le]
      _ ≤ ∫⁻ z in e.target, ENNReal.ofReal (ν z) *
            ENNReal.ofReal ((‖eval (blockPt d (e.symm z)) f‖ / d.A.h (blockPt d (e.symm z)) ^ n) ^ 2) :=
          lintegral_mono_set inter_subset_left
      _ ≤ _ := lintegral_chart_le e d.dV hνs.continuousOn hνV hgm
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ D := by positivity
  have h2 : ENNReal.ofReal ((‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2) ≤
      ENNReal.ofReal (max C₀ 0 * (n : ℝ) ^ D * blockL2NormComplex d n f ^ 2) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    exact key.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hn0)) hint)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

end BlockResolutionImageSup

open BlockResolutionImageSup in

theorem BlockResolutionImageSup.proof (hC : ChartSupBound.Statement) : BlockResolutionImageSup.Statement := by
  intro D K _ _ ι _ Ω _ _ d
  choose N hNo hxN C hC0 hCb using fun x => local_bound hC d x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover N hNo fun x _ => mem_iUnion.2 ⟨x, hxN x⟩
  refine ⟨Real.sqrt (∑ x ∈ t, C x), fun n hn f hf y => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht (mem_univ y))
  have hS : C x ≤ ∑ x ∈ t, C x := Finset.single_le_sum (fun i _ => hC0 i) hxt
  have hS0 : 0 ≤ ∑ x ∈ t, C x := Finset.sum_nonneg fun i _ => hC0 i
  have hr0 : 0 ≤ blockL2NormComplex d n f := Real.sqrt_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ D := by positivity
  have h2 : (‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2 ≤
      (∑ x ∈ t, C x) * (n : ℝ) ^ D * blockL2NormComplex d n f ^ 2 :=
    (hCb x n hn f hf y hyx).trans (by gcongr)
  have hp : 0 ≤ ‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n :=
    div_nonneg (norm_nonneg _) (pow_nonneg (d.A.pos _ (lift_blockNonzero d (d.R.mem_U y))).le n)
  have hpow : Real.sqrt ((n : ℝ) ^ D) = (n : ℝ) ^ ((D : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    ring_nf
  calc ‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n
      = Real.sqrt ((‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2) := (Real.sqrt_sq hp).symm
    _ ≤ Real.sqrt ((∑ x ∈ t, C x) * (n : ℝ) ^ D * blockL2NormComplex d n f ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (∑ x ∈ t, C x) * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2NormComplex d n f := by
      rw [Real.sqrt_mul (mul_nonneg hS0 hn0), Real.sqrt_mul hS0, Real.sqrt_sq hr0, hpow]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
