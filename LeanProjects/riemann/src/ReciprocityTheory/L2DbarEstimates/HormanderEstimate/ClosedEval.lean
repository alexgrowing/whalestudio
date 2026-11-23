import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.ExistsLintegralCompactLe

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

noncomputable section

theorem evalPt (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hMV : C.MVStatement) :
    EvalPtStatement n M := by
  intro z hz ψ hψ x0
  obtain ⟨e, hx0, hze⟩ := hz x0
  have he : IsChart n z e := fun x _ => by rw [hze]
  have hte : e x0 ∈ e.target := e.map_source hx0
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 e.open_target (e x0) hte
  have hcb : Metric.closedBall (e x0) (r / 2) ⊆ e.target :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hrt
  set K : Set M := e.symm '' Metric.closedBall (e x0) (r / 2) with hKdef
  have hKc : IsCompact K :=
    (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono hcb)
  have hKs : K ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_target (hcb hy)
  obtain ⟨c, hc⟩ := exists_lintegral_compact_le n z ψ hψ K hKc
  set Vb : ℝ≥0∞ := volume (Metric.ball (e x0) (r / 2)) with hVbdef
  have hVpos : 0 < Vb := Metric.measure_ball_pos _ _ (half_pos hr)
  have hVfin : Vb ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨max c 0 / Vb.toReal, div_nonneg (le_max_right c 0) ENNReal.toReal_nonneg,
    fun F hF => ?_⟩
  have hFc : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨e', hx', hze'⟩ := hz x
    have he' : IsChart n z e' := fun y _ => by rw [hze']
    have h1 : ContinuousAt (F ∘ e'.symm) (e' x) :=
      (hF e' he').continuousOn.continuousAt (e'.open_target.mem_nhds (e'.map_source hx'))
    have h3 := h1.comp (e'.continuousAt hx')
    apply h3.congr
    filter_upwards [e'.open_source.mem_nhds hx'] with y hy
    simp [Function.comp, e'.left_inv hy]
  set f : M → ℝ≥0∞ := K.indicator (fun x => ‖F x‖ₑ ^ 2) with hfdef
  have hfm : Measurable f :=
    (hFc.measurable.enorm.pow_const 2).indicator hKc.isClosed.measurableSet
  have hdiff : DifferentiableOn ℂ (F ∘ e.symm) (Metric.ball (e x0) (r / 2)) :=
    (hF e he).mono (Metric.ball_subset_closedBall.trans hcb)
  have h1 := hMV n (e x0) (r / 2) (F ∘ e.symm) (fun _ => 1) hdiff measurable_const
  simp only [mul_one, lintegral_const, Measure.restrict_apply_univ, Function.comp_apply,
    e.left_inv hx0] at h1
  have h2 : ∫⁻ y in Metric.ball (e x0) (r / 2), ‖F (e.symm y)‖ₑ ^ 2 ≤
      ∫⁻ y in e.target, f (e.symm y) := by
    rw [← lintegral_indicator (hs := Metric.isOpen_ball.measurableSet),
      ← lintegral_indicator (hs := e.open_target.measurableSet)]
    apply lintegral_mono
    intro y
    by_cases hy : y ∈ Metric.ball (e x0) (r / 2)
    · have hyt : y ∈ e.target := hcb (Metric.ball_subset_closedBall hy)
      have hyK : e.symm y ∈ K := ⟨y, Metric.ball_subset_closedBall hy, rfl⟩
      simp [Set.indicator_apply, hy, hyt, hyK, hfdef]
    · simp [Set.indicator_apply, hy]
  have h3 : ∫⁻ y in e.target, f (e.symm y) = ∫⁻ x, f x ∂vol n z := by
    refine (lintegral_vol_chart n z hz e he f hfm (fun x hx => ?_)).symm
    have hxK : x ∉ K := fun h => hx (hKs h)
    simp [hfdef, Set.indicator_apply, hxK]
  have h4 : ∫⁻ x, f x ∂vol n z = ∫⁻ x in K, ‖F x‖ₑ ^ 2 ∂vol n z := by
    rw [hfdef, lintegral_indicator (hs := hKc.isClosed.measurableSet)]
  have h5 : ∫⁻ x in K, ‖F x‖ₑ ^ 2 ∂vol n z ≤ ENNReal.ofReal (max c 0) * wint n z F ψ :=
    (hc F).trans (by gcongr; exact le_max_left c 0)
  have hfin : ‖F x0‖ₑ ^ 2 * Vb ≤ ENNReal.ofReal (max c 0) * wint n z F ψ := by
    have h6 := h1.trans (h2.trans (h3.le.trans (h4.le.trans h5)))
    rwa [one_mul] at h6
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm,
    ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hVpos.ne' hVfin), ENNReal.ofReal_toReal hVfin,
    div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl hVpos.ne') (Or.inl hVfin)]
  exact hfin

end

end ReciprocityTheory.L2DbarEstimates.F
