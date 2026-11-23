import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsSphereLongitude
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory Set
open scoped ENNReal Pointwise

noncomputable section

lemma SphereLongitudeCoordinates.norm_vector_three_eq_sqrt (u v w : ℝ) :
    ‖(!₂[u, v, w] : E3)‖ = Real.sqrt (u ^ 2 + v ^ 2 + w ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp [sq_abs, add_assoc]

lemma SphereLongitudeCoordinates.cyl_point {ρ : ℝ} (hρ : 0 < ρ) (φ z : ℝ) :
    ‖(!₂[ρ * Real.cos φ, ρ * Real.sin φ, z] : E3)‖ = Real.sqrt (ρ ^ 2 + z ^ 2) ∧
    (Real.sqrt (ρ ^ 2 + z ^ 2))⁻¹ • (!₂[ρ * Real.cos φ, ρ * Real.sin φ, z] : E3) =
      spherePoint (z / Real.sqrt (ρ ^ 2 + z ^ 2)) φ := by
  have hn : (ρ * Real.cos φ) ^ 2 + (ρ * Real.sin φ) ^ 2 + z ^ 2 = ρ ^ 2 + z ^ 2 := by
    have := Real.cos_sq_add_sin_sq φ
    linear_combination ρ ^ 2 * this
  refine ⟨by rw [SphereLongitudeCoordinates.norm_vector_three_eq_sqrt, hn], ?_⟩
  set r := Real.sqrt (ρ ^ 2 + z ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = ρ ^ 2 + z ^ 2 := Real.sq_sqrt (by positivity)
  have hs : Real.sqrt (1 - (z / r) ^ 2) = ρ / r := by
    rw [show 1 - (z / r) ^ 2 = (ρ / r) ^ 2 by field_simp; linarith]
    exact Real.sqrt_sq (div_pos hρ hr0).le
  ext i
  fin_cases i <;> simp [spherePoint, hs] <;> field_simp

lemma SphereLongitudeCoordinates.height_subst {ρ : ℝ} (hρ : 0 < ρ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ z, (if ρ ^ 2 + z ^ 2 < 1 then g (z / Real.sqrt (ρ ^ 2 + z ^ 2)) else 0) =
      ∫⁻ c in Ioo (-1 : ℝ) 1, ENNReal.ofReal (ρ / Real.sqrt (1 - c ^ 2) ^ 3) *
        (if ρ ^ 2 < 1 - c ^ 2 then g c else 0) := by
  set f : ℝ → ℝ := fun c => ρ * c / Real.sqrt (1 - c ^ 2) with hf
  have hpos : ∀ c ∈ Ioo (-1 : ℝ) 1, 0 < 1 - c ^ 2 := fun c hc => by
    have : c ^ 2 < 1 := by nlinarith [hc.1, hc.2]
    linarith
  have key : ∀ c ∈ Ioo (-1 : ℝ) 1,
      Real.sqrt (ρ ^ 2 + f c ^ 2) = ρ / Real.sqrt (1 - c ^ 2) ∧
      f c / Real.sqrt (ρ ^ 2 + f c ^ 2) = c := by
    intro c hc
    have hw : 0 < Real.sqrt (1 - c ^ 2) := Real.sqrt_pos.2 (hpos c hc)
    have hw2 : Real.sqrt (1 - c ^ 2) ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (hpos c hc).le
    have e1 : ρ ^ 2 + f c ^ 2 = (ρ / Real.sqrt (1 - c ^ 2)) ^ 2 := by
      simp only [hf]
      field_simp
      linear_combination hw2
    have e2 : Real.sqrt (ρ ^ 2 + f c ^ 2) = ρ / Real.sqrt (1 - c ^ 2) := by
      rw [e1]; exact Real.sqrt_sq (div_pos hρ hw).le
    refine ⟨e2, ?_⟩
    rw [e2]; simp only [hf]; field_simp
  have himg : f '' Ioo (-1 : ℝ) 1 = univ := by
    refine eq_univ_of_forall fun z => ?_
    set r := Real.sqrt (ρ ^ 2 + z ^ 2)
    have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
    have hr2 : r ^ 2 = ρ ^ 2 + z ^ 2 := Real.sq_sqrt (by positivity)
    have hc2 : (z / r) ^ 2 < 1 := by
      rw [div_pow, div_lt_one (by positivity)]; nlinarith
    have hc : z / r ∈ Ioo (-1 : ℝ) 1 := by
      have := abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hc2)
      exact ⟨this.1, this.2⟩
    refine ⟨z / r, hc, ?_⟩
    have hs : Real.sqrt (1 - (z / r) ^ 2) = ρ / r := by
      rw [show 1 - (z / r) ^ 2 = (ρ / r) ^ 2 by field_simp; linarith]
      exact Real.sqrt_sq (div_pos hρ hr0).le
    simp only [hf, hs]
    field_simp
  have hinj : InjOn f (Ioo (-1 : ℝ) 1) := fun a ha b hb hab => by
    rw [← (key a ha).2, ← (key b hb).2, hab]
  have hderiv : ∀ c ∈ Ioo (-1 : ℝ) 1,
      HasDerivWithinAt f (ρ / Real.sqrt (1 - c ^ 2) ^ 3) (Ioo (-1 : ℝ) 1) c := by
    intro c hc
    have hw : 0 < Real.sqrt (1 - c ^ 2) := Real.sqrt_pos.2 (hpos c hc)
    have hw2 : Real.sqrt (1 - c ^ 2) ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (hpos c hc).le
    have h1 : HasDerivAt (fun c : ℝ => 1 - c ^ 2) (-(2 * c)) c := by
      simpa using (hasDerivAt_pow 2 c).const_sub 1
    have h2 := h1.sqrt (hpos c hc).ne'
    have h3 := ((hasDerivAt_id c).const_mul ρ).div h2 hw.ne'
    have h4 : HasDerivAt f ((ρ * 1 * Real.sqrt (1 - c ^ 2) - ρ * id c * (-(2 * c) /
        (2 * Real.sqrt (1 - c ^ 2)))) / Real.sqrt (1 - c ^ 2) ^ 2) c := h3
    refine (h4.congr_deriv ?_).hasDerivWithinAt
    simp only [id, mul_one]
    field_simp
    linear_combination hw2
  rw [← setLIntegral_univ, ← himg,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv hinj]
  refine setLIntegral_congr_fun measurableSet_Ioo fun c hc => ?_
  have hw : 0 < Real.sqrt (1 - c ^ 2) := Real.sqrt_pos.2 (hpos c hc)
  have hw2 : Real.sqrt (1 - c ^ 2) ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (hpos c hc).le
  rw [abs_of_pos (by positivity), (key c hc).2]
  congr 1
  have e : ρ ^ 2 + f c ^ 2 < 1 ↔ ρ ^ 2 < 1 - c ^ 2 := by
    have h1c := (hpos c hc).ne'
    have e1 : ρ ^ 2 + f c ^ 2 = ρ ^ 2 / (1 - c ^ 2) := by
      simp only [hf]; rw [div_pow, hw2]; field_simp; ring
    rw [e1, div_lt_one (hpos c hc)]
  simp only [e]

lemma SphereLongitudeCoordinates.radial_pow {w : ℝ} (hw : 0 < w) :
    ∫⁻ ρ in Ioo 0 w, ENNReal.ofReal (ρ ^ 2 / w ^ 3) = 3⁻¹ := by
  have hint : IntegrableOn (fun ρ : ℝ => ρ ^ 2 / w ^ 3) (Ioo 0 w) :=
    ((continuous_pow 2).div_const _).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ρ => by positivity), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hw.le, intervalIntegral.integral_div, integral_pow]
  have : ((w ^ (2 + 1) - 0 ^ (2 + 1)) / (((2 : ℕ) : ℝ) + 1) / w ^ 3 : ℝ) = 3⁻¹ := by
    push_cast; field_simp; ring
  rw [this, ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

lemma SphereLongitudeCoordinates.radial (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ *
        ∫⁻ z, (if ρ ^ 2 + z ^ 2 < 1 then g (z / Real.sqrt (ρ ^ 2 + z ^ 2)) else 0) =
      3⁻¹ * ∫⁻ c in Ioo (-1 : ℝ) 1, g c := by
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 *
      (ENNReal.ofReal (p.1 / Real.sqrt (1 - p.2 ^ 2) ^ 3) *
        (if p.1 ^ 2 < 1 - p.2 ^ 2 then g p.2 else 0))) := by
    refine (by fun_prop : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1).mul
      ((by fun_prop : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal (p.1 / Real.sqrt (1 - p.2 ^ 2) ^ 3)).mul
      (Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (hg.comp measurable_snd)
        measurable_const))
  calc _ = ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ c in Ioo (-1 : ℝ) 1, ENNReal.ofReal ρ *
          (ENNReal.ofReal (ρ / Real.sqrt (1 - c ^ 2) ^ 3) *
            (if ρ ^ 2 < 1 - c ^ 2 then g c else 0)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
        rw [SphereLongitudeCoordinates.height_subst hρ,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ c in Ioo (-1 : ℝ) 1, ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ *
          (ENNReal.ofReal (ρ / Real.sqrt (1 - c ^ 2) ^ 3) *
            (if ρ ^ 2 < 1 - c ^ 2 then g c else 0)) :=
        lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ c in Ioo (-1 : ℝ) 1, 3⁻¹ * g c := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun c hc => ?_
        have hpos : 0 < 1 - c ^ 2 := by nlinarith [hc.1, hc.2]
        set w := Real.sqrt (1 - c ^ 2) with hwdef
        have hw : 0 < w := Real.sqrt_pos.2 hpos
        calc _ = ∫⁻ ρ in Ioi (0 : ℝ),
              (Iio w).indicator (fun ρ => ENNReal.ofReal (ρ ^ 2 / w ^ 3)) ρ * g c := by
              refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
              have e : ρ ^ 2 < 1 - c ^ 2 ↔ ρ ∈ Iio w := by
                rw [mem_Iio, hwdef, Real.lt_sqrt (le_of_lt hρ)]
              by_cases h : ρ ^ 2 < 1 - c ^ 2
              · rw [if_pos h, indicator_of_mem (e.1 h), ← mul_assoc,
                  ← ENNReal.ofReal_mul (le_of_lt hρ)]
                congr 2
                ring
              · rw [if_neg h, indicator_of_notMem (fun h' => h (e.2 h'))]
                simp
          _ = (∫⁻ ρ in Ioi (0 : ℝ),
              (Iio w).indicator (fun ρ => ENNReal.ofReal (ρ ^ 2 / w ^ 3)) ρ) * g c :=
              lintegral_mul_const _ ((by fun_prop : Measurable fun ρ : ℝ =>
                ENNReal.ofReal (ρ ^ 2 / w ^ 3)).indicator measurableSet_Iio)
          _ = 3⁻¹ * g c := by
              rw [setLIntegral_indicator measurableSet_Iio, inter_comm, Ioi_inter_Iio,
                SphereLongitudeCoordinates.radial_pow hw]
    _ = 3⁻¹ * ∫⁻ c in Ioo (-1 : ℝ) 1, g c := lintegral_const_mul _ hg

lemma SphereLongitudeCoordinates.continuous_spherePoint :
    Continuous fun p : ℝ × ℝ => spherePoint p.1 p.2 := by
  unfold spherePoint
  fun_prop

lemma SphereLongitudeCoordinates.measurePreserving_coords :
    MeasurePreserving (fun y : ℝ × (ℝ × ℝ) => (!₂[y.2.1, y.2.2, y.1] : E3)) := by
  have h := (PiLp.volume_preserving_toLp (Fin 3)).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm.comp
      ((MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ).symm))
  convert h using 1
  all_goals first
    | exact Measure.volume_eq_prod _ _
    | (funext y; ext i; fin_cases i <;> rfl)

lemma SphereLongitudeCoordinates.cone_volume {s : Set E3} (hs : MeasurableSet s) :
    3 * volume {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ ‖x‖⁻¹ • x ∈ s} =
      ∫⁻ φ in Ioo (-Real.pi) Real.pi, ∫⁻ c in Ioo (-1 : ℝ) 1,
        s.indicator 1 (spherePoint c φ) := by
  set C := {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ ‖x‖⁻¹ • x ∈ s} with hCdef
  have hC : MeasurableSet C :=
    (measurableSet_lt measurable_const measurable_norm).inter
      ((measurableSet_lt measurable_norm measurable_const).inter
        ((by fun_prop : Measurable fun x : E3 => ‖x‖⁻¹ • x) hs))
  set G : ℝ × ℝ → ℝ≥0∞ := fun p => s.indicator 1 (spherePoint p.1 p.2) with hGdef
  have hG : Measurable G :=
    (measurable_one.indicator hs).comp SphereLongitudeCoordinates.continuous_spherePoint.measurable
  set H : (ℝ × ℝ) × ℝ → ℝ≥0∞ := fun w => if w.1.1 ^ 2 + w.2 ^ 2 < 1 then
    G (w.2 / Real.sqrt (w.1.1 ^ 2 + w.2 ^ 2), w.1.2) else 0 with hHdef
  have hH : Measurable H :=
    Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (hG.comp (by fun_prop))
      measurable_const
  have hpt : ∀ p ∈ polarCoord.target, ∀ z : ℝ,
      C.indicator 1 (!₂[p.1 * Real.cos p.2, p.1 * Real.sin p.2, z] : E3) = H (p, z) := by
    intro p hp z
    have hρ : 0 < p.1 := hp.1
    obtain ⟨hn, hd⟩ := SphereLongitudeCoordinates.cyl_point hρ p.2 z
    have hr : 0 < Real.sqrt (p.1 ^ 2 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hlt : Real.sqrt (p.1 ^ 2 + z ^ 2) < 1 ↔ p.1 ^ 2 + z ^ 2 < 1 := by
      rw [Real.sqrt_lt' one_pos, one_pow]
    have hmem : (!₂[p.1 * Real.cos p.2, p.1 * Real.sin p.2, z] : E3) ∈ C ↔
        p.1 ^ 2 + z ^ 2 < 1 ∧ spherePoint (z / Real.sqrt (p.1 ^ 2 + z ^ 2)) p.2 ∈ s := by
      show 0 < ‖_‖ ∧ ‖_‖ < 1 ∧ ‖_‖⁻¹ • _ ∈ s ↔ _
      rw [hn, hd, hlt]
      exact ⟨fun h => h.2, fun h => ⟨hr, h⟩⟩
    change C.indicator 1 _ = if p.1 ^ 2 + z ^ 2 < 1 then
      s.indicator 1 (spherePoint (z / Real.sqrt (p.1 ^ 2 + z ^ 2)) p.2) else 0
    by_cases h1 : p.1 ^ 2 + z ^ 2 < 1 <;>
      by_cases h2 : spherePoint (z / Real.sqrt (p.1 ^ 2 + z ^ 2)) p.2 ∈ s
    · rw [if_pos h1, indicator_of_mem (hmem.2 ⟨h1, h2⟩), indicator_of_mem h2]
      rfl
    · rw [if_pos h1, indicator_of_notMem (fun h => h2 (hmem.1 h).2), indicator_of_notMem h2]
    · rw [if_neg h1, indicator_of_notMem (fun h => h1 (hmem.1 h).1)]
    · rw [if_neg h1, indicator_of_notMem (fun h => h1 (hmem.1 h).1)]
  have hK : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 * ∫⁻ z, H (p, z) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1).mul hH.lintegral_prod_right'
  have step : volume C =
      ∫⁻ φ in Ioo (-Real.pi) Real.pi, 3⁻¹ * ∫⁻ c in Ioo (-1 : ℝ) 1, G (c, φ) := by
    calc volume C = ∫⁻ x, C.indicator 1 x := (lintegral_indicator_one hC).symm
    _ = ∫⁻ y : ℝ × (ℝ × ℝ), C.indicator 1 (!₂[y.2.1, y.2.2, y.1] : E3) :=
        (SphereLongitudeCoordinates.measurePreserving_coords.lintegral_comp
          (measurable_one.indicator hC)).symm
    _ = ∫⁻ q : ℝ × ℝ, ∫⁻ z, C.indicator 1 (!₂[q.1, q.2, z] : E3) := by
        rw [Measure.volume_eq_prod, lintegral_prod_symm]
        exact ((measurable_one.indicator hC).comp
          SphereLongitudeCoordinates.measurePreserving_coords.measurable).aemeasurable
    _ = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 * ∫⁻ z, H (p, z) := by
        rw [← lintegral_comp_polarCoord_symm
          (fun q : ℝ × ℝ => ∫⁻ z, C.indicator 1 (!₂[q.1, q.2, z] : E3))]
        refine setLIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
        simp only [polarCoord_symm_apply, smul_eq_mul]
        congr 1
        exact lintegral_congr fun z => hpt p hp z
    _ = ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ φ in Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal ρ * ∫⁻ z, H ((ρ, φ), z) := by
        rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
          lintegral_prod _ hK.aemeasurable]
    _ = ∫⁻ φ in Ioo (-Real.pi) Real.pi, ∫⁻ ρ in Ioi (0 : ℝ),
          ENNReal.ofReal ρ * ∫⁻ z, H ((ρ, φ), z) :=
        lintegral_lintegral_swap hK.aemeasurable
    _ = _ := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun φ _ => ?_
        exact SphereLongitudeCoordinates.radial (fun c => G (c, φ)) (hG.comp (by fun_prop))
  rw [step, lintegral_const_mul' _ _ (by simp), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

lemma SphereLongitudeCoordinates.cone_eq (s : Set E3) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((↑) ⁻¹' s : Set Sphere2) : Set E3) =
      {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ ‖x‖⁻¹ • x ∈ s} := by
  ext x
  constructor
  · rintro ⟨a, ha, _, ⟨n, hn, rfl⟩, rfl⟩
    have h1 : ‖(n : E3)‖ = 1 := by simp
    have hna : ‖a • (n : E3)‖ = a := by rw [norm_smul, h1, mul_one, Real.norm_of_nonneg ha.1.le]
    refine ⟨by rw [hna]; exact ha.1, by rw [hna]; exact ha.2, ?_⟩
    rw [hna, smul_smul, inv_mul_cancel₀ ha.1.ne', one_smul]
    exact hn
  · rintro ⟨h0, h1, h2⟩
    have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E3) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h0.ne']
    exact ⟨‖x‖, ⟨h0, h1⟩, ‖x‖⁻¹ • x, ⟨⟨_, hu⟩, h2, rfl⟩, smul_inv_smul₀ h0.ne' x⟩

lemma SphereLongitudeCoordinates.spherePoint_add_two_pi (c φ : ℝ) :
    spherePoint c (φ + 2 * Real.pi) = spherePoint c φ := by
  simp [spherePoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma SphereLongitudeCoordinates.toSphere_preimage {s : Set E3} (hs : MeasurableSet s) :
    (volume : Measure E3).toSphere ((↑) ⁻¹' s) =
      ∫⁻ φ in Ioc 0 (2 * Real.pi), ∫⁻ c in Icc (-1 : ℝ) 1, s.indicator 1 (spherePoint c φ) := by
  rw [Measure.toSphere_apply' _ (measurable_subtype_coe hs), finrank_euclideanSpace_fin,
    SphereLongitudeCoordinates.cone_eq]
  push_cast
  rw [SphereLongitudeCoordinates.cone_volume hs]
  set h : ℝ → ℝ≥0∞ := fun φ => ∫⁻ c in Icc (-1 : ℝ) 1, s.indicator 1 (spherePoint c φ) with hh
  have hper : Function.Periodic h (2 * Real.pi) := fun φ => by
    simp only [hh, SphereLongitudeCoordinates.spherePoint_add_two_pi]
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  calc ∫⁻ φ in Ioo (-Real.pi) Real.pi, ∫⁻ c in Ioo (-1 : ℝ) 1, s.indicator 1 (spherePoint c φ)
      = ∫⁻ φ in Ioc (-Real.pi) (-Real.pi + 2 * Real.pi), h φ := by
        rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
        rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        refine lintegral_congr fun φ => ?_
        simp only [hh]
        rw [Measure.restrict_congr_set Ioo_ae_eq_Icc]
    _ = ∫⁻ b : AddCircle (2 * Real.pi), hper.lift b := by
        rw [← AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi)]
        rfl
    _ = ∫⁻ φ in Ioc 0 (0 + 2 * Real.pi), h φ := by
        rw [← AddCircle.lintegral_preimage (2 * Real.pi) 0]
        rfl
    _ = _ := by rw [zero_add]

lemma SphereLongitudeCoordinates.toSphere_map :
    ((volume : Measure E3).toSphere).map (fun n : Sphere2 => (n : E3)) =
      (volume.restrict (Icc (-1 : ℝ) 1 ×ˢ Ioc 0 (2 * Real.pi))).map
        (fun p : ℝ × ℝ => spherePoint p.1 p.2) := by
  have hc := SphereLongitudeCoordinates.continuous_spherePoint
  ext s hs
  rw [Measure.map_apply measurable_subtype_coe hs,
    SphereLongitudeCoordinates.toSphere_preimage hs, ← lintegral_indicator_one hs,
    lintegral_map (measurable_one.indicator hs) hc.measurable, Measure.volume_eq_prod,
    ← Measure.prod_restrict]
  have hm : Measurable fun p : ℝ × ℝ => s.indicator (1 : E3 → ℝ≥0∞) (spherePoint p.1 p.2) :=
    (measurable_one.indicator hs).comp hc.measurable
  rw [lintegral_prod _ hm.aemeasurable]
  exact (lintegral_lintegral_swap (f := fun c φ => s.indicator (1 : E3 → ℝ≥0∞) (spherePoint c φ))
    hm.aemeasurable).symm

theorem SphereLongitudeCoordinates.proof : SphereLongitudeCoordinates.Statement := by
  have hc := SphereLongitudeCoordinates.continuous_spherePoint
  have hM := SphereLongitudeCoordinates.toSphere_map
  have huniv : (volume : Measure E3).toSphere univ = ENNReal.ofReal (4 * Real.pi) := by
    have := congrArg (fun μ : Measure E3 => μ univ) hM
    beta_reduce at this
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ,
      Measure.map_apply hc.measurable MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ] at this
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Ioc,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  unfold SphereLongitudeCoordinates.Statement sphereMeasure
  rw [Measure.map_smul, hM, huniv]

end

end GroundTheory.Heights₂.Heights.FlagBundles
