import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaA

open MeasureTheory Set Real
open scoped ENNReal Pointwise

namespace ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume

noncomputable def coneFun (G : ℝ → ℝ≥0∞) (z s : ℝ) : ℝ≥0∞ :=
  if 0 < z ^ 2 + s ∧ z ^ 2 + s < 1 then G (z / Real.sqrt (z ^ 2 + s)) else 0

lemma measurable_coneFun {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    Measurable (fun p : ℝ × ℝ => coneFun G p.1 p.2) := by
  unfold coneFun
  refine Measurable.ite ?_ (hG.comp ?_) measurable_const
  · exact (measurableSet_lt (f := fun _ : ℝ × ℝ => (0 : ℝ)) (g := fun p : ℝ × ℝ => p.1 ^ 2 + p.2)
      measurable_const (by fun_prop)).inter (measurableSet_lt (g := fun _ : ℝ × ℝ => (1 : ℝ))
      (f := fun p : ℝ × ℝ => p.1 ^ 2 + p.2) (by fun_prop) measurable_const)
  · fun_prop

lemma lintegral_cylindrical (H : ℝ × (ℝ × ℝ) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ x : E3, H (x 0, (x 1, x 2)) = ∫⁻ z : ℝ, ∫⁻ p : ℝ × ℝ, H (z, p) := by
  have hΦ : MeasurePreserving (fun x : E3 => (x 0, (x 1, x 2))) volume volume := by
    have h1 := PiLp.volume_preserving_ofLp (Fin 3)
    have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
    have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod
      (volume_preserving_finTwoArrow ℝ)
    have := h3.comp (h2.comp h1)
    have hf : (fun x : E3 => (x 0, (x 1, x 2))) = Prod.map id MeasurableEquiv.finTwoArrow ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ∘ WithLp.ofLp := by
      funext x; rfl
    rw [hf, Measure.volume_eq_prod]
    exact this
  rw [hΦ.lintegral_comp hH, Measure.volume_eq_prod, lintegral_prod _ hH.aemeasurable]

lemma lintegral_plane_polar (K : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ p : ℝ × ℝ, K p =
      ∫⁻ q in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal q.1 * K (q.1 * cos q.2, q.1 * sin q.2) := by
  rw [← lintegral_comp_polarCoord_symm]
  rfl

lemma lintegral_theta (G : ℝ → ℝ≥0∞) :
    ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (sin θ) * G (cos θ) = ∫⁻ t in Ioo (-1 : ℝ) 1, G t := by
  have h1 : ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (sin θ) * G (cos θ) =
      ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (sin θ) * G (cos θ) := by
    rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
    congr 1
    funext θ
    by_cases h0 : θ ∈ Ioo 0 π
    · have : θ ∈ Ioo (-π) π := ⟨by linarith [h0.1, pi_pos], h0.2⟩
      simp [indicator_of_mem h0, indicator_of_mem this]
    · rw [indicator_of_notMem h0]
      by_cases h1 : θ ∈ Ioo (-π) π
      · rw [indicator_of_mem h1]
        have hθ : θ ≤ 0 := by
          by_contra h
          exact h0 ⟨lt_of_not_ge h, h1.2⟩
        have : sin θ ≤ 0 := sin_nonpos_of_nonpos_of_neg_pi_le hθ h1.1.le
        simp [ENNReal.ofReal_of_nonpos this]
      · rw [indicator_of_notMem h1]
  have h2 : cos '' Ioo 0 π = Ioo (-1 : ℝ) 1 := cosPartialHomeomorph.image_source_eq_target
  rw [h1, ← h2, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (f' := fun x => -sin x) (fun x _ => (hasDerivAt_cos x).hasDerivWithinAt)
    (injOn_cos.mono Ioo_subset_Icc_self)]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
  rw [abs_neg, abs_of_pos (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)]

lemma lintegral_Ioi_ofReal_mul (F : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * F r = ∫⁻ r, ENNReal.ofReal r * F r := by
  rw [← lintegral_indicator measurableSet_Ioi]
  congr 1
  funext r
  by_cases hr : r ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hr]
  · rw [indicator_of_notMem hr, ENNReal.ofReal_of_nonpos (not_lt.mp hr), zero_mul]

lemma lintegral_coneFun (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x : E3, coneFun G (x 0) ((x 1) ^ 2 + (x 2) ^ 2) =
      volume (Ioo (-π) π) * (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * (Iio (1 : ℝ)).indicator 1 r) *
        ∫⁻ t in Ioo (-1 : ℝ) 1, G t := by
  have hN := measurable_coneFun hG
  rw [lintegral_cylindrical (fun q => coneFun G q.1 (q.2.1 ^ 2 + q.2.2 ^ 2))
    (hN.comp (by fun_prop : Measurable fun q : ℝ × (ℝ × ℝ) => (q.1, q.2.1 ^ 2 + q.2.2 ^ 2)))]
  have hin : ∀ z : ℝ, ∫⁻ p : ℝ × ℝ, coneFun G z (p.1 ^ 2 + p.2 ^ 2) =
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * coneFun G z (r ^ 2)) * volume (Ioo (-π) π) := by
    intro z
    rw [lintegral_plane_polar]
    have h : ∀ q : ℝ × ℝ, ENNReal.ofReal q.1 *
        coneFun G z ((q.1 * cos q.2) ^ 2 + (q.1 * sin q.2) ^ 2) =
        (ENNReal.ofReal q.1 * coneFun G z (q.1 ^ 2)) * (fun _ : ℝ => (1 : ℝ≥0∞)) q.2 := by
      intro q
      have : (q.1 * cos q.2) ^ 2 + (q.1 * sin q.2) ^ 2 = q.1 ^ 2 := by
        calc _ = q.1 ^ 2 * (sin q.2 ^ 2 + cos q.2 ^ 2) := by ring
          _ = q.1 ^ 2 := by rw [sin_sq_add_cos_sq, mul_one]
      rw [this, mul_one]
    simp_rw [h]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_mul
      (f := fun r : ℝ => ENNReal.ofReal r * coneFun G z (r ^ 2)) (g := fun _ : ℝ => (1 : ℝ≥0∞))
      ((by fun_prop : Measurable fun r : ℝ => ENNReal.ofReal r).mul
        (hN.comp (by fun_prop : Measurable fun r : ℝ => (z, r ^ 2)))).aemeasurable
      aemeasurable_const, lintegral_one, Measure.restrict_apply_univ]
  simp_rw [hin]
  rw [lintegral_mul_const' _ _ measure_Ioo_lt_top.ne]
  simp_rw [lintegral_Ioi_ofReal_mul]
  have hprod : ∫⁻ z : ℝ, ∫⁻ r : ℝ, ENNReal.ofReal r * coneFun G z (r ^ 2) =
      ∫⁻ q : ℝ × ℝ, ENNReal.ofReal q.2 * coneFun G q.1 (q.2 ^ 2) := by
    have hm : Measurable fun q : ℝ × ℝ => ENNReal.ofReal q.2 * coneFun G q.1 (q.2 ^ 2) :=
      (by fun_prop : Measurable fun q : ℝ × ℝ => ENNReal.ofReal q.2).mul
        (hN.comp (by fun_prop : Measurable fun q : ℝ × ℝ => (q.1, q.2 ^ 2)))
    rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  rw [hprod, lintegral_plane_polar]
  have hset : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := measurableSet_Ioi.prod measurableSet_Ioo
  rw [setLIntegral_congr_fun hset (g := fun q : ℝ × ℝ =>
      (ENNReal.ofReal (q.1 ^ 2) * (Iio (1 : ℝ)).indicator 1 q.1) *
        (ENNReal.ofReal (sin q.2) * G (cos q.2))) ?_]
  · rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_mul
      (f := fun r : ℝ => ENNReal.ofReal (r ^ 2) * (Iio (1 : ℝ)).indicator 1 r)
      (g := fun θ : ℝ => ENNReal.ofReal (sin θ) * G (cos θ)) (by
        refine ((by fun_prop : Measurable fun r : ℝ => ENNReal.ofReal (r ^ 2)).mul ?_).aemeasurable
        exact measurable_const.indicator measurableSet_Iio)
      ((by fun_prop : Measurable fun θ : ℝ => ENNReal.ofReal (sin θ)).mul
        (hG.comp continuous_cos.measurable)).aemeasurable, lintegral_theta]
    ring
  · rintro ⟨r, θ⟩ ⟨hr, -⟩
    simp only at hr ⊢
    have hr : 0 < r := hr
    have hs : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
      calc _ = r ^ 2 * (sin θ ^ 2 + cos θ ^ 2) := by ring
        _ = r ^ 2 := by rw [sin_sq_add_cos_sq, mul_one]
    have e1 : ENNReal.ofReal r * ENNReal.ofReal (r * sin θ) =
        ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (sin θ) := by
      rw [← ENNReal.ofReal_mul hr.le, ← ENNReal.ofReal_mul (sq_nonneg r)]
      ring_nf
    unfold coneFun
    rw [hs, Real.sqrt_sq hr.le, mul_div_cancel_left₀ _ hr.ne']
    by_cases h1 : r < 1
    · have h2 : r ^ 2 < 1 := by nlinarith
      rw [if_pos ⟨by positivity, h2⟩, indicator_of_mem (show r ∈ Iio (1 : ℝ) from h1)]
      rw [← mul_assoc, e1]
      simp only [Pi.one_apply, mul_one]
      ring
    · have h2 : ¬ r ^ 2 < 1 := by nlinarith
      rw [if_neg (fun h => h2 h.2), indicator_of_notMem (show r ∉ Iio (1 : ℝ) from h1)]
      simp

noncomputable def coneConst : ℝ≥0∞ :=
  volume (Ioo (-π) π) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * (Iio (1 : ℝ)).indicator 1 r

lemma norm_eq_sqrt_coord (y : E3) : ‖y‖ = Real.sqrt (y 0 ^ 2 + (y 1 ^ 2 + y 2 ^ 2)) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  ring_nf

lemma measurableSet_cone0 {s : Set ℝ} (hs : MeasurableSet s) :
    MeasurableSet {y : E3 | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ y 0 / ‖y‖ ∈ s} := by
  refine (measurableSet_lt measurable_const measurable_norm).inter
    ((measurableSet_lt measurable_norm measurable_const).inter ?_)
  exact (by fun_prop : Measurable fun y : E3 => y 0 / ‖y‖) hs

lemma volume_cone0 {s : Set ℝ} (hs : MeasurableSet s) :
    volume {y : E3 | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ y 0 / ‖y‖ ∈ s} =
      coneConst * volume (s ∩ Ioo (-1 : ℝ) 1) := by
  rw [← lintegral_indicator_one (measurableSet_cone0 hs)]
  have h : ∀ y : E3, {y : E3 | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ y 0 / ‖y‖ ∈ s}.indicator 1 y =
      coneFun (s.indicator 1) (y 0) ((y 1) ^ 2 + (y 2) ^ 2) := by
    intro y
    have hn := norm_eq_sqrt_coord y
    set S := y 0 ^ 2 + (y 1 ^ 2 + y 2 ^ 2) with hS
    have hS0 : 0 ≤ S := by positivity
    unfold coneFun
    by_cases hc : 0 < S ∧ S < 1
    · rw [if_pos hc]
      have h0 : 0 < ‖y‖ := by rw [hn]; exact Real.sqrt_pos.2 hc.1
      have h1 : ‖y‖ < 1 := by
        rw [hn, ← Real.sqrt_one]; exact Real.sqrt_lt_sqrt hS0 hc.2
      by_cases hy : y 0 / ‖y‖ ∈ s
      · rw [indicator_of_mem (show y ∈ {y : E3 | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ y 0 / ‖y‖ ∈ s} from
          ⟨h0, h1, hy⟩), ← hn, indicator_of_mem hy]
        rfl
      · rw [indicator_of_notMem (fun h => hy h.2.2), ← hn, indicator_of_notMem hy]
    · rw [if_neg hc, indicator_of_notMem]
      rintro ⟨h0, h1, -⟩
      apply hc
      rw [hn] at h0 h1
      refine ⟨Real.sqrt_pos.1 h0, ?_⟩
      nlinarith [Real.sq_sqrt hS0, Real.sqrt_nonneg S]
  simp_rw [h]
  rw [lintegral_coneFun (s.indicator 1) (measurable_one.indicator hs), lintegral_indicator_one hs,
    Measure.restrict_apply hs, coneConst]

lemma volume_cone {u : E3} (hu : ‖u‖ = 1) {s : Set ℝ} (hs : MeasurableSet s) :
    volume {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ inner ℝ x u / ‖x‖ ∈ s} =
      coneConst * volume (s ∩ Ioo (-1 : ℝ) 1) := by
  set e0 : E3 := EuclideanSpace.single 0 1
  have he0 : ‖e0‖ = 1 := by simp [e0]
  set L : E3 ≃ₗᵢ[ℝ] E3 := (ℝ ∙ (u - e0))ᗮ.reflection
  have hLu : L u = e0 := Submodule.reflection_sub (by rw [hu, he0])
  have hL0 : ∀ x : E3, (L x) 0 = inner ℝ x u := by
    intro x
    rw [← L.inner_map_map, hLu]
    simp [e0, EuclideanSpace.inner_single_right]
  have hset : {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ inner ℝ x u / ‖x‖ ∈ s} =
      L ⁻¹' {y : E3 | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ y 0 / ‖y‖ ∈ s} := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, LinearIsometryEquiv.norm_map, hL0]
  rw [hset, L.measurePreserving.measure_preimage (measurableSet_cone0 hs).nullMeasurableSet,
    volume_cone0 hs]

lemma cone_eq (u : E3) (s : Set ℝ) :
    Ioo (0 : ℝ) 1 • (((↑) : S2 → E3) '' {n : S2 | inner ℝ (n : E3) u ∈ s}) =
      {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ inner ℝ x u / ‖x‖ ∈ s} := by
  ext x
  constructor
  · rintro ⟨a, ha, _, ⟨n, hn, rfl⟩, rfl⟩
    have hn1 : ‖(n : E3)‖ = 1 := by simp
    have ha0 : 0 < a := ha.1
    simp only [mem_ofPred_eq] at hn ⊢
    rw [norm_smul, hn1, Real.norm_eq_abs, abs_of_pos ha0, mul_one, real_inner_smul_left,
      mul_div_cancel_left₀ _ ha0.ne']
    exact ⟨ha0, ha.2, hn⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨‖x‖, ⟨h0, h1⟩, ‖x‖⁻¹ • x, ⟨⟨‖x‖⁻¹ • x, ?_⟩, ?_, rfl⟩, ?_⟩
    · simp [norm_smul, h0.ne']
    · show inner ℝ (‖x‖⁻¹ • x) u ∈ s
      rw [real_inner_smul_left, inv_mul_eq_div]
      exact h2
    · exact smul_inv_smul₀ h0.ne' x

lemma toSphere_univ_ne_zero : (volume : Measure E3).toSphere univ ≠ 0 :=
  Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero _)

lemma toSphere_univ_ne_top : (volume : Measure E3).toSphere univ ≠ ⊤ :=
  measure_ne_top _ _

lemma map_inner_sphereMeasure {u : E3} (hu : ‖u‖ = 1) :
    sphereMeasure.map (fun n : S2 => inner ℝ (n : E3) u) =
      (2⁻¹ : ℝ≥0∞) • volume.restrict (Ioo (-1 : ℝ) 1) := by
  have hφ : Measurable (fun n : S2 => inner ℝ (n : E3) u) := by fun_prop
  set c := (volume : Measure E3).toSphere univ
  set K : ℝ≥0∞ := c⁻¹ * (Module.finrank ℝ E3 * coneConst)
  have key : ∀ s : Set ℝ, MeasurableSet s →
      sphereMeasure.map (fun n : S2 => inner ℝ (n : E3) u) s =
        K * volume.restrict (Ioo (-1 : ℝ) 1) s := by
    intro s hs
    rw [Measure.map_apply hφ hs, sphereMeasure, Measure.smul_apply, smul_eq_mul,
      Measure.toSphere_apply' _ (hφ hs)]
    rw [show (fun n : S2 => inner ℝ (n : E3) u) ⁻¹' s = {n : S2 | inner ℝ (n : E3) u ∈ s} from rfl,
      cone_eq, volume_cone hu hs, Measure.restrict_apply hs]
    simp only [K, c]
    ring
  have hK : K = 2⁻¹ := by
    apply ENNReal.eq_inv_of_mul_eq_one_left
    have h1 := key univ MeasurableSet.univ
    rw [Measure.map_apply hφ MeasurableSet.univ, preimage_univ, sphereMeasure,
      Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel toSphere_univ_ne_zero
      toSphere_univ_ne_top, Measure.restrict_apply_univ, Real.volume_Ioo] at h1
    rw [h1]
    norm_num
  ext s hs
  rw [key s hs, hK, Measure.smul_apply, smul_eq_mul]

end ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume

namespace ReciprocityTheory.ChartRestriction.G.AI

open ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume

theorem arch0 (u : E3) (f : ℝ → ℝ) (hu : ‖u‖ = 1) (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1) :
    MeasureTheory.Integrable (fun n : S2 => f (inner ℝ (n : E3) u)) sphereMeasure ∧
    ∫ n : S2, f (inner ℝ (n : E3) u) ∂sphereMeasure = (1 / 2) * ∫ t in (-1 : ℝ)..1, f t := by
  have hφ : Measurable (fun n : S2 => inner ℝ (n : E3) u) := by fun_prop
  have hmap := map_inner_sphereMeasure hu
  have hIoo : IntegrableOn f (Ioo (-1 : ℝ) 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hf).mono_set Ioo_subset_Ioc_self
  have hint : Integrable f ((2⁻¹ : ℝ≥0∞) • volume.restrict (Ioo (-1 : ℝ) 1)) :=
    hIoo.smul_measure (by simp)
  rw [← hmap] at hint
  refine ⟨(integrable_map_measure hint.aestronglyMeasurable hφ.aemeasurable).1 hint, ?_⟩
  rw [← integral_map hφ.aemeasurable hint.aestronglyMeasurable, hmap, integral_smul_measure,
    intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  simp

end ReciprocityTheory.ChartRestriction.G.AI
