import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenSt

open MeasureTheory Set Filter Topology InnerProductSpace intervalIntegral
open scoped Laplacian

namespace ReciprocityTheory.AnForm.A.GreenFunction

noncomputable section

def ee (θ : ℝ) : ℂ := Real.cos θ + Real.sin θ * Complex.I

theorem hasDerivAt_ee (θ : ℝ) : HasDerivAt ee (Complex.I * ee θ) θ := by
  have h := ((Real.hasDerivAt_cos θ).ofReal_comp).add
    (((Real.hasDerivAt_sin θ).ofReal_comp).mul_const Complex.I)
  have e : Complex.I * ee θ = ((-Real.sin θ : ℝ) : ℂ) + (Real.cos θ : ℂ) * Complex.I := by
    simp only [ee, Complex.ofReal_neg]
    linear_combination (Real.sin θ : ℂ) * Complex.I_sq
  rw [e]; exact h

theorem continuous_ee : Continuous ee := by unfold ee; fun_prop

theorem ee_smul (θ : ℝ) : ee θ = Real.cos θ • (1 : ℂ) + Real.sin θ • Complex.I := by
  simp [ee, Complex.real_smul]

theorem iee_smul (θ : ℝ) :
    Complex.I * ee θ = (-Real.sin θ) • (1 : ℂ) + Real.cos θ • Complex.I := by
  simp only [ee, Complex.real_smul, Complex.ofReal_neg]
  linear_combination (Real.sin θ : ℂ) * Complex.I_sq

theorem norm_ee (θ : ℝ) : ‖ee θ‖ = 1 := by
  have : ee θ = Complex.exp (θ * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; rfl
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem ee_pi : ee Real.pi = ee (-Real.pi) := by
  unfold ee; rw [Real.cos_neg, Real.sin_neg, Real.sin_pi]; simp

theorem polar_symm_eq (p : ℝ × ℝ) : Complex.polarCoord.symm p = p.1 • ee p.2 := by
  simp [ee, Complex.real_smul]; ring

theorem laplacian_eq_fderiv_fderiv (u : ℂ → ℝ) (z : ℂ) :
    Δ u z = fderiv ℝ (fderiv ℝ u) z 1 1 + fderiv ℝ (fderiv ℝ u) z Complex.I Complex.I := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp [iteratedFDeriv_two_apply]

theorem lap_eq_rot (u : ℂ → ℝ) (z : ℂ) (θ : ℝ) :
    Δ u z = fderiv ℝ (fderiv ℝ u) z (ee θ) (ee θ)
      + fderiv ℝ (fderiv ℝ u) z (Complex.I * ee θ) (Complex.I * ee θ) := by
  rw [laplacian_eq_fderiv_fderiv, iee_smul, ee_smul]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  have hsc := Real.sin_sq_add_cos_sq θ
  set H := fderiv ℝ (fderiv ℝ u) z
  linear_combination (-(H 1 1 + H Complex.I Complex.I)) * hsc

section calc1

variable {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (a : ℂ)
include hu

theorem contDiff_fderiv1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)

theorem continuous_fderiv_fderiv : Continuous (fderiv ℝ (fderiv ℝ u)) :=
  (contDiff_fderiv1 hu).continuous_fderiv one_ne_zero

theorem continuous_fderiv_of_contDiff_two : Continuous (fderiv ℝ u) := (contDiff_fderiv1 hu).continuous

theorem hasDerivAt_rad (e : ℂ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => u (a + r • e)) (fderiv ℝ u (a + r • e) e) r := by
  have hp : HasDerivAt (fun r : ℝ => a + r • e) e r := by
    simpa using ((hasDerivAt_id r).smul_const e).const_add a
  exact ((hu.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt r hp

theorem hasDerivAt_rad' (e : ℂ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => fderiv ℝ u (a + r • e) e)
      (fderiv ℝ (fderiv ℝ u) (a + r • e) e e) r := by
  have hp : HasDerivAt (fun r : ℝ => a + r • e) e r := by
    simpa using ((hasDerivAt_id r).smul_const e).const_add a
  have h2 := (((contDiff_fderiv1 hu).differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt r hp
  simpa using h2.clm_apply (hasDerivAt_const r e)

theorem hasDerivAt_ang (r θ : ℝ) :
    HasDerivAt (fun θ : ℝ => u (a + r • ee θ))
      (fderiv ℝ u (a + r • ee θ) (r • (Complex.I * ee θ))) θ := by
  have hp : HasDerivAt (fun θ : ℝ => a + r • ee θ) (r • (Complex.I * ee θ)) θ :=
    ((hasDerivAt_ee θ).const_smul r).const_add a
  exact ((hu.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt θ hp

theorem hasDerivAt_ang' (r θ : ℝ) :
    HasDerivAt (fun θ : ℝ => fderiv ℝ u (a + r • ee θ) (r • (Complex.I * ee θ)))
      (fderiv ℝ (fderiv ℝ u) (a + r • ee θ) (r • (Complex.I * ee θ)) (r • (Complex.I * ee θ))
        - r * fderiv ℝ u (a + r • ee θ) (ee θ)) θ := by
  have hp : HasDerivAt (fun θ : ℝ => a + r • ee θ) (r • (Complex.I * ee θ)) θ :=
    ((hasDerivAt_ee θ).const_smul r).const_add a
  have hq : HasDerivAt (fun θ : ℝ => r • (Complex.I * ee θ)) (r • (Complex.I * (Complex.I * ee θ))) θ :=
    ((hasDerivAt_ee θ).const_mul Complex.I).const_smul r
  have h2 := (((contDiff_fderiv1 hu).differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt θ hp
  refine (h2.clm_apply hq).congr_deriv ?_
  rw [← mul_assoc, Complex.I_mul_I]
  simp only [neg_one_mul, smul_neg, map_neg, map_smul, smul_eq_mul, sub_eq_add_neg]
  rfl

end calc1

def Arad (u : ℂ → ℝ) (a : ℂ) (θ r : ℝ) : ℝ :=
  Real.log r * (r * fderiv ℝ (fderiv ℝ u) (a + r • ee θ) (ee θ) (ee θ)
    + fderiv ℝ u (a + r • ee θ) (ee θ))

def AngularPart (u : ℂ → ℝ) (a : ℂ) (r θ : ℝ) : ℝ :=
  Real.log r * (r * fderiv ℝ (fderiv ℝ u) (a + r • ee θ) (Complex.I * ee θ) (Complex.I * ee θ)
    - fderiv ℝ u (a + r • ee θ) (ee θ))

theorem decomp (u : ℂ → ℝ) (a : ℂ) (r θ : ℝ) :
    r * Real.log r * Δ u (a + r • ee θ) = Arad u a θ r + AngularPart u a r θ := by
  rw [lap_eq_rot u _ θ]; simp only [Arad, AngularPart]; ring

theorem vanish {u : ℂ → ℝ} {a : ℂ} {R : ℝ} (hR : ∀ z, R ≤ ‖z - a‖ → u z = 0) {z : ℂ}
    (hz : R < ‖z - a‖) : fderiv ℝ u z = 0 ∧ fderiv ℝ (fderiv ℝ u) z = 0 := by
  have hU : IsOpen {y : ℂ | R < ‖y - a‖} := isOpen_lt continuous_const (by fun_prop)
  have h1 : ∀ y ∈ {y : ℂ | R < ‖y - a‖}, fderiv ℝ u y = 0 := by
    intro y hy
    have : u =ᶠ[𝓝 y] fun _ => 0 :=
      Filter.eventually_of_mem (hU.mem_nhds hy) (fun x hx => hR x (le_of_lt hx))
    rw [this.fderiv_eq]; simp
  refine ⟨h1 z hz, ?_⟩
  have : fderiv ℝ u =ᶠ[𝓝 z] fun _ => 0 := Filter.eventually_of_mem (hU.mem_nhds hz) h1
  rw [this.fderiv_eq]; simp

theorem norm_rad (a : ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖a + r • ee θ - a‖ = r := by
  simp [norm_ee, abs_of_nonneg hr]

theorem integral_Arad {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (a : ℂ) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ z, R ≤ ‖z - a‖ → u z = 0) (θ : ℝ) :
    ∫ r in Ioi 0, Arad u a θ r = u a := by
  have hz : ∀ r, R < r → Arad u a θ r = 0 := fun r hr => by
    obtain ⟨h1, h2⟩ := vanish hR (z := a + r • ee θ) (by rw [norm_rad a (by linarith) θ]; exact hr)
    simp only [Arad, h1, h2, ContinuousLinearMap.zero_apply, mul_zero, add_zero]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioc_subset_Ioi_self : Ioc (0:ℝ) (R + 1) ⊆ Ioi 0)
    (fun r hr => hz r (by
      simp only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at hr; linarith [hr.2 hr.1]))]
  rw [← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ R + 1)]
  have hD1 := continuous_fderiv_of_contDiff_two hu
  have hD2 := continuous_fderiv_fderiv hu
  have he := continuous_ee
  have hF : ∀ r ∈ Ioo (0:ℝ) (R + 1), HasDerivAt
      (fun r => r * Real.log r * fderiv ℝ u (a + r • ee θ) (ee θ) - u (a + r • ee θ))
      (Arad u a θ r) r := by
    intro r hr
    have := ((Real.hasDerivAt_mul_log hr.1.ne').mul (hasDerivAt_rad' hu a (ee θ) r)).sub
      (hasDerivAt_rad hu a (ee θ) r)
    refine this.congr_deriv ?_
    simp only [Arad]; ring
  have hcont : ContinuousOn
      (fun r : ℝ => r * Real.log r * fderiv ℝ u (a + r • ee θ) (ee θ) - u (a + r • ee θ))
      (Icc 0 (R + 1)) := by
    apply Continuous.continuousOn
    have h0 := hu.continuous
    have hg : Continuous fun r : ℝ => fderiv ℝ u (a + r • ee θ) (ee θ) := by fun_prop
    exact (Real.continuous_mul_log.mul hg).sub (by fun_prop)
  have hint : IntervalIntegrable (Arad u a θ) volume 0 (R + 1) := by
    have hP : Continuous (fun r : ℝ => r * fderiv ℝ (fderiv ℝ u) (a + r • ee θ) (ee θ) (ee θ)
        + fderiv ℝ u (a + r • ee θ) (ee θ)) := by fun_prop
    exact intervalIntegrable_log'.mul_continuousOn hP.continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hcont hF hint]
  obtain ⟨h1, -⟩ := vanish hR (z := a + (R + 1) • ee θ)
    (by rw [norm_rad a (by linarith) θ]; linarith)
  have h0 : u (a + (R + 1) • ee θ) = 0 := hR _ (by rw [norm_rad a (by linarith) θ]; linarith)
  rw [h1, h0]; simp

theorem integral_Bang_eq_zero {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (a : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ θ in Ioo (-Real.pi) Real.pi, AngularPart u a r θ = 0 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hB : ∀ θ, AngularPart u a r θ = (Real.log r / r) *
      (fderiv ℝ (fderiv ℝ u) (a + r • ee θ) (r • (Complex.I * ee θ)) (r • (Complex.I * ee θ))
        - r * fderiv ℝ u (a + r • ee θ) (ee θ)) := by
    intro θ
    simp only [AngularPart, map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    field_simp
  simp_rw [hB]
  have hD1 := continuous_fderiv_of_contDiff_two hu
  have hD2 := continuous_fderiv_fderiv hu
  have he := continuous_ee
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hasDerivAt_ang' hu a r θ)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [ee_pi]; simp

theorem integrableOn_log_mul {P : ℝ × ℝ → ℝ} (hP : Continuous P) {R : ℝ} (hR0 : 0 < R)
    (hz : ∀ p : ℝ × ℝ, R < p.1 → P p = 0) :
    IntegrableOn (fun p : ℝ × ℝ => Real.log p.1 * P p) (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
  have hpi := Real.pi_pos
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc 0 R ×ˢ Icc (-Real.pi) Real.pi)).exists_bound_of_continuousOn hP.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _)
    (hC (0, 0) ⟨⟨le_rfl, hR0.le⟩, ⟨by linarith, by linarith⟩⟩)
  have hg : IntegrableOn (fun p : ℝ × ℝ =>
      C * (Ioc 0 R).indicator (fun r => ‖Real.log r‖) p.1 * (1 : ℝ))
      (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    have h1 : Integrable (fun r : ℝ => C * (Ioc 0 R).indicator (fun r => ‖Real.log r‖) r)
        (volume.restrict (Ioi 0)) := by
      apply Integrable.const_mul
      apply Integrable.mono_measure _ Measure.restrict_le_self
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR0.le).1 intervalIntegrable_log').norm
    have h2 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
      integrableOn_const (by simp)
    exact Integrable.mul_prod (f := fun r : ℝ => C * (Ioc 0 R).indicator (fun r => ‖Real.log r‖) r)
      (g := fun _ : ℝ => (1 : ℝ)) h1 h2
  refine hg.mono' ((Real.measurable_log.comp measurable_fst).mul hP.measurable).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
  rcases le_or_gt p.1 R with h | h
  · have h1 : p.1 ∈ Ioc 0 R := ⟨hp.1, h⟩
    rw [indicator_of_mem h1, mul_one, norm_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC p ⟨⟨le_of_lt hp.1, h⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩)
      (norm_nonneg _)
  · rw [hz p h, mul_zero, norm_zero]
    exact mul_nonneg (mul_nonneg hC0 (indicator_nonneg (fun _ _ => norm_nonneg _) _)) zero_le_one

theorem continuous_lap {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) : Continuous (Δ u) := by
  have h : Δ u = fun z =>
      fderiv ℝ (fderiv ℝ u) z 1 1 + fderiv ℝ (fderiv ℝ u) z Complex.I Complex.I :=
    funext (laplacian_eq_fderiv_fderiv u)
  have hD2 := continuous_fderiv_fderiv hu
  rw [h]; fun_prop

theorem lap_vanish {u : ℂ → ℝ} {a : ℂ} {R : ℝ} (hR : ∀ z, R ≤ ‖z - a‖ → u z = 0) {z : ℂ}
    (hz : R < ‖z - a‖) : Δ u z = 0 := by
  rw [laplacian_eq_fderiv_fderiv, (vanish hR hz).2]; simp

theorem integrable_log_norm_ball {R : ℝ} (hR0 : 0 < R) :
    Integrable (fun z : ℂ => (Iic R).indicator (fun t => ‖Real.log t‖) ‖z‖) := by
  rw [integrable_fun_norm_addHaar volume (f := (Iic R).indicator (fun t => ‖Real.log t‖)),
    Complex.finrank_real_complex]
  have hcont : ContinuousOn (fun y : ℝ => ‖y * Real.log y‖) (Icc 0 R) :=
    (Real.continuous_mul_log.norm).continuousOn
  have h1 : IntegrableOn (fun y : ℝ => ‖y * Real.log y‖) (Ioc 0 R) :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun y : ℝ => y ^ (2 - 1) • (Iic R).indicator (fun t => ‖Real.log t‖) y)
      (Ioc 0 R) :=
    h1.congr_fun (fun y hy => by
      simp [indicator_of_mem (show y ∈ Iic R from hy.2), abs_of_pos hy.1]) measurableSet_Ioc
  have h3 : IntegrableOn (fun y : ℝ => y ^ (2 - 1) • (Iic R).indicator (fun t => ‖Real.log t‖) y)
      (Ioi R) :=
    (integrableOn_zero).congr_fun (fun y hy => by
      simp [indicator_of_notMem (show y ∉ Iic R by simp only [mem_Iic, not_le]; exact hy)]) measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi hR0.le]
  exact h2.union h3

theorem green_at {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (a : ℂ) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ z, R ≤ ‖z - a‖ → u z = 0) :
    Integrable (fun z : ℂ => Real.log ‖z - a‖ * Δ u z) ∧
      ∫ z : ℂ, Real.log ‖z - a‖ * Δ u z = 2 * Real.pi * u a := by
  have hpi := Real.pi_pos
  have hD1 := continuous_fderiv_of_contDiff_two hu
  have hD2 := continuous_fderiv_fderiv hu
  have he := continuous_ee
  have hL := continuous_lap hu
  constructor
  · obtain ⟨C, hC⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn hL.continuousOn
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC a (Metric.mem_closedBall_self hR0.le))
    have hg : Integrable (fun z : ℂ => C * (Iic R).indicator (fun t => ‖Real.log t‖) ‖z - a‖) :=
      ((integrable_log_norm_ball hR0).comp_sub_right a).const_mul C
    refine hg.mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact ((Real.measurable_log.comp (measurable_norm.comp (measurable_id.sub_const a))).mul
        hL.measurable).aestronglyMeasurable
    · rcases le_or_gt ‖z - a‖ R with h | h
      · rw [indicator_of_mem (show ‖z - a‖ ∈ Iic R from h), norm_mul, mul_comm C]
        exact mul_le_mul_of_nonneg_left
          (hC z (by rwa [Metric.mem_closedBall, dist_eq_norm])) (norm_nonneg _)
      · rw [lap_vanish hR h, mul_zero, norm_zero]
        exact mul_nonneg hC0 (indicator_nonneg (fun _ _ => norm_nonneg _) _)
  · have ht := integral_add_left_eq_self (μ := volume) (fun z : ℂ => Real.log ‖z - a‖ * Δ u z) a
    simp only [add_sub_cancel_left] at ht
    rw [← ht]
    rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
    have htarget : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :=
      measurableSet_Ioi.prod measurableSet_Ioo
    rw [setIntegral_congr_fun htarget
      (g := fun p : ℝ × ℝ => Arad u a p.2 p.1 + AngularPart u a p.1 p.2) (fun p hp => by
        simp only [polar_symm_eq, smul_eq_mul]
        rw [norm_smul, norm_ee, mul_one, Real.norm_eq_abs, abs_of_pos hp.1, ← decomp]; ring)]
    have hA : IntegrableOn (fun p : ℝ × ℝ => Arad u a p.2 p.1) (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) :=
      integrableOn_log_mul (P := fun p : ℝ × ℝ =>
        p.1 * fderiv ℝ (fderiv ℝ u) (a + p.1 • ee p.2) (ee p.2) (ee p.2)
          + fderiv ℝ u (a + p.1 • ee p.2) (ee p.2)) (by fun_prop) hR0 (fun p hp => by
        obtain ⟨h1, h2⟩ := vanish hR (z := a + p.1 • ee p.2)
          (by rw [norm_rad a (by linarith) p.2]; exact hp)
        simp only [h1, h2, ContinuousLinearMap.zero_apply, mul_zero, add_zero])
    have hB : IntegrableOn (fun p : ℝ × ℝ => AngularPart u a p.1 p.2) (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) :=
      integrableOn_log_mul (P := fun p : ℝ × ℝ =>
        p.1 * fderiv ℝ (fderiv ℝ u) (a + p.1 • ee p.2) (Complex.I * ee p.2) (Complex.I * ee p.2)
          - fderiv ℝ u (a + p.1 • ee p.2) (ee p.2)) (by fun_prop) hR0 (fun p hp => by
        obtain ⟨h1, h2⟩ := vanish hR (z := a + p.1 • ee p.2)
          (by rw [norm_rad a (by linarith) p.2]; exact hp)
        simp only [h1, h2, ContinuousLinearMap.zero_apply, mul_zero, sub_zero])
    rw [integral_add hA hB]
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hA hB
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hA,
      integral_prod _ hB]
    have eA : ∀ θ : ℝ, ∫ r in Ioi 0, Arad u a θ r = u a := integral_Arad hu a hR0 hR
    have eB : ∫ r in Ioi (0:ℝ), ∫ θ in Ioo (-Real.pi) Real.pi, AngularPart u a r θ = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioi (fun r hr => integral_Bang_eq_zero hu a hr)]
      simp
    simp only [eA, eB, add_zero, setIntegral_const, smul_eq_mul]
    rw [Real.volume_real_Ioo_of_le (by linarith)]
    ring

end

end ReciprocityTheory.AnForm.A.GreenFunction
