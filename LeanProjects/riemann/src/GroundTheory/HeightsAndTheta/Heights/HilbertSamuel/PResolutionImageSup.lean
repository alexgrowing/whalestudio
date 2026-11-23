import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionImageSup
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartSup
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionSupBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Set Filter Topology

noncomputable section

namespace ResolutionImageSup

theorem analyticOnNhd_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} {V : Set E}
    {g : E → ι → ℂ} (hg : ∀ i, AnalyticOnNhd ℂ (fun w => g w i) V) (f : MvPolynomial ι ℂ) :
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

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem lift_ne_zero (d : HSMDatum D Ω κ) {x y : d.R.X} (hy : y ∈ d.R.U x) : d.R.lift x y ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := (d.R.mem x y hy).1 ()
  exact hi (by rw [h]; rfl)

theorem ptNorm_resPt_eq (d : HSMDatum D Ω κ) {n : ℕ} {f : MvPolynomial (Ix κ) ℂ} (hf : f.IsHomogeneous n)
    {x y : d.R.X} (hy : y ∈ d.R.U x) :
    ptNorm d.m (RingHom.id ℂ) n f (resPt d y) = ptNorm d.m (RingHom.id ℂ) n f (d.R.lift x y) := by
  obtain ⟨c, hc, hcy⟩ := d.R.compat y x y ⟨d.R.mem_U y, hy⟩
  have h : resPt d y = c () • d.R.lift x y := by
    rw [resPt, hcy]
    rfl
  rw [h, ResolutionSupBound.ptNorm_smul d.m hf (hc ())]

theorem continuous_ptNorm_resPt (d : HSMDatum D Ω κ) {n : ℕ} {f : MvPolynomial (Ix κ) ℂ}
    (hf : f.IsHomogeneous n) : Continuous fun y => ptNorm d.m (RingHom.id ℂ) n f (resPt d y) := by
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
  have hne := lift_ne_zero d (d.R.mem_U y₀)
  have hρ : ContinuousAt d.m.ρ (d.R.lift y₀ y₀) :=
    d.smooth.continuousOn.continuousAt (isOpen_ne.mem_nhds hne)
  have hcont : ContinuousAt (fun y => ptNorm d.m (RingHom.id ℂ) n f (d.R.lift y₀ y)) y₀ := by
    unfold ptNorm
    simp only [MvPolynomial.map_id]
    exact (((MvPolynomial.continuous_eval f).continuousAt.comp hL).norm).div ((hρ.comp hL).pow n)
      (pow_pos (d.m.pos _ hne) n).ne'
  refine hcont.congr ?_
  filter_upwards [(d.R.isOpen_U y₀).mem_nhds (d.R.mem_U y₀)] with y hy
  exact (ptNorm_resPt_eq d hf hy).symm

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

theorem local_bound (hC : ChartSupBound.Statement) (d : HSMDatum D Ω κ) (x₀ : d.R.X) :
    ∃ N : Set d.R.X, IsOpen N ∧ x₀ ∈ N ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ f : MvPolynomial (Ix κ) ℂ, f.IsHomogeneous n → ∀ y ∈ N,
        ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ≤ C * (n : ℝ) ^ D * resolutionVolumeL2Complex d n f ^ 2 := by
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
  have hLne : ∀ w ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀, d.R.lift x₀ (e.symm w) ≠ 0 :=
    fun w hw => lift_ne_zero d hw.2
  have hψ : ContDiffOn ℝ 2 (fun w => 2 * Real.log (d.m.ρ (d.R.lift x₀ (e.symm w))))
      (e.target ∩ e.symm ⁻¹' d.R.U x₀) := by
    have hL2 : ContDiffOn ℝ 2 (fun w => d.R.lift x₀ (e.symm w)) (e.target ∩ e.symm ⁻¹' d.R.U x₀) :=
      contDiffOn_pi.2 fun p => ((hLa p).contDiffOn_of_completeSpace).restrict_scalars ℝ
    have hρ : ContDiffOn ℝ 2 (fun w => d.m.ρ (d.R.lift x₀ (e.symm w))) (e.target ∩ e.symm ⁻¹' d.R.U x₀) :=
      (d.smooth.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).comp hL2 fun w hw => hLne w hw
    exact contDiffOn_const.mul (hρ.log fun w hw => (d.m.pos _ (hLne w hw)).ne')
  obtain ⟨C₀, hC₀⟩ := hC D (e.target ∩ e.symm ⁻¹' d.R.U x₀) (Metric.closedBall (e x₀) (δ / 2)) _ ν hVo
    (isCompact_closedBall _ _) hKV hψ (hνs.continuousOn.mono inter_subset_left) fun z hz => hνpos z hz.1
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e x₀) (δ / 2), e.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨hj, Metric.mem_ball_self (half_pos hδ)⟩, max C₀ 0, le_max_right _ _, fun n hn f hf y hy => ?_⟩
  have hgc := (continuous_ptNorm_resPt d hf).pow 2
  have hgm : Measurable fun y => ENNReal.ofReal (ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2) :=
    ENNReal.measurable_ofReal.comp hgc.measurable
  have hgi : Integrable (fun y => ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2) d.dV :=
    hgc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI0 : 0 ≤ ∫ y, ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ∂d.dV :=
    integral_nonneg fun y => sq_nonneg _
  have hres : resolutionVolumeL2Complex d n f ^ 2 = ∫ y, ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ∂d.dV := by
    rw [resolutionVolumeL2Complex, Real.sq_sqrt hI0]
  have hid : ∀ w ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀,
      ‖eval (d.R.lift x₀ (e.symm w)) f‖ ^ 2 *
          Real.exp (-(n : ℝ) * (2 * Real.log (d.m.ρ (d.R.lift x₀ (e.symm w))))) =
        ptNorm d.m (RingHom.id ℂ) n f (resPt d (e.symm w)) ^ 2 := by
    intro w hw
    rw [ptNorm_resPt_eq d hf hw.2]
    simp only [ptNorm, MvPolynomial.map_id]
    exact (sq_div_pow_eq (d.m.pos _ (hLne w hw)) n).symm
  have key := hC₀ n hn _ (analyticOnNhd_eval hLa f) (e y) (Metric.ball_subset_closedBall hy.2)
  have hyV : e y ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀ := hKV (Metric.ball_subset_closedBall hy.2)
  rw [hid _ hyV, e.left_inv hy.1] at key
  have hint : ∫⁻ z in e.target ∩ e.symm ⁻¹' d.R.U x₀,
      ENNReal.ofReal (‖eval (d.R.lift x₀ (e.symm z)) f‖ ^ 2 *
        Real.exp (-(n : ℝ) * (2 * Real.log (d.m.ρ (d.R.lift x₀ (e.symm z))))) * ν z) ≤
      ENNReal.ofReal (resolutionVolumeL2Complex d n f ^ 2) := by
    rw [hres, ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun y => sq_nonneg _)]
    calc _ = ∫⁻ z in e.target ∩ e.symm ⁻¹' d.R.U x₀, ENNReal.ofReal (ν z) *
            ENNReal.ofReal (ptNorm d.m (RingHom.id ℂ) n f (resPt d (e.symm z)) ^ 2) := by
          refine setLIntegral_congr_fun hVo.measurableSet fun z hz => ?_
          rw [hid z hz, mul_comm, ENNReal.ofReal_mul (hνpos z hz.1).le]
      _ ≤ ∫⁻ z in e.target, ENNReal.ofReal (ν z) *
            ENNReal.ofReal (ptNorm d.m (RingHom.id ℂ) n f (resPt d (e.symm z)) ^ 2) :=
          lintegral_mono_set inter_subset_left
      _ ≤ _ := lintegral_chart_le e d.dV hνs.continuousOn hνV hgm
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ D := by positivity
  have h2 : ENNReal.ofReal (ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2) ≤
      ENNReal.ofReal (max C₀ 0 * (n : ℝ) ^ D * resolutionVolumeL2Complex d n f ^ 2) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    exact key.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hn0)) hint)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

end ResolutionImageSup

open ResolutionImageSup in

theorem ResolutionImageSup.proof (hC : ChartSupBound.Statement) : ResolutionImageSup.Statement := by
  intro D Ω _ _ κ _ d
  choose N hNo hxN C hC0 hCb using fun x => local_bound hC d x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover N hNo fun x _ => mem_iUnion.2 ⟨x, hxN x⟩
  refine ⟨Real.sqrt (∑ x ∈ t, C x), fun n hn f hf y => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht (mem_univ y))
  have hS : C x ≤ ∑ x ∈ t, C x := Finset.single_le_sum (fun i _ => hC0 i) hxt
  have hS0 : 0 ≤ ∑ x ∈ t, C x := Finset.sum_nonneg fun i _ => hC0 i
  have hr0 : 0 ≤ resolutionVolumeL2Complex d n f := Real.sqrt_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ D := by positivity
  have h2 : ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ≤
      (∑ x ∈ t, C x) * (n : ℝ) ^ D * resolutionVolumeL2Complex d n f ^ 2 :=
    (hCb x n hn f hf y hyx).trans (by gcongr)
  have hp : 0 ≤ ptNorm d.m (RingHom.id ℂ) n f (resPt d y) :=
    div_nonneg (norm_nonneg _) (pow_nonneg (d.m.pos _ (lift_ne_zero d (d.R.mem_U y))).le n)
  have hpow : Real.sqrt ((n : ℝ) ^ D) = (n : ℝ) ^ ((D : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    ring_nf
  calc ptNorm d.m (RingHom.id ℂ) n f (resPt d y)
      = Real.sqrt (ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2) := (Real.sqrt_sq hp).symm
    _ ≤ Real.sqrt ((∑ x ∈ t, C x) * (n : ℝ) ^ D * resolutionVolumeL2Complex d n f ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (∑ x ∈ t, C x) * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f := by
      rw [Real.sqrt_mul (mul_nonneg hS0 hn0), Real.sqrt_mul hS0, Real.sqrt_sq hr0, hpow]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
