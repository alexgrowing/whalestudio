import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Ad3 Ad3.S MeasureTheory Complex Filter Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfIntegral

lemma KK_one_eq (α β : ℂ) (t : ℝ) :
    KK α β 1 t = ((1 : ℂ) + (-I) * t) ^ (-α) * ((1 : ℂ) + I * t) ^ (-β) := by
  simp [KK, sub_eq_add_neg]

lemma mem_slit (c : ℂ) (hc : c.re = 0) (t : ℝ) : (1 : ℂ) + c * t ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simp [hc]

lemma hasDerivAt_factor (a c : ℂ) (hc : c.re = 0) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ((1 : ℂ) + c * u) ^ (-a))
      (-a * c * ((1 : ℂ) + c * t) ^ (-(a + 1))) t := by
  have h1 : HasDerivAt (fun z : ℂ => 1 + c * z) c (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).const_mul c).const_add 1
  have h2 := (h1.cpow_const (c := -a) (mem_slit c hc t)).comp_ofReal
  have e : -a - 1 = -(a + 1) := by ring
  rw [e] at h2
  convert h2 using 1
  ring

lemma hasDerivAt_KK (α β : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => KK α β 1 u)
      (I * α * KK (α + 1) β 1 t - I * β * KK α (β + 1) 1 t) t := by
  have h1 := hasDerivAt_factor α (-I) (by simp) t
  have h2 := hasDerivAt_factor β I (by simp) t
  have h3 := h1.mul h2
  have e : (fun u : ℝ => KK α β 1 u) =
      (fun u : ℝ => ((1 : ℂ) + (-I) * u) ^ (-α) * ((1 : ℂ) + I * u) ^ (-β)) := by
    funext u; exact KK_one_eq α β u
  rw [e]
  refine HasDerivAt.congr_deriv (f := fun u : ℝ => ((1 : ℂ) + (-I) * u) ^ (-α) * ((1 : ℂ) + I * u) ^ (-β)) h3 ?_
  rw [KK_one_eq, KK_one_eq]
  ring

lemma continuous_KK (α β : ℂ) : Continuous fun t : ℝ => KK α β 1 t :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_KK α β t).continuousAt

lemma norm_cpow_le (z w : ℂ) (hz : z ≠ 0) :
    ‖z ^ w‖ ≤ ‖z‖ ^ w.re * Real.exp (Real.pi * |w.im|) := by
  rw [Complex.norm_cpow_of_ne_zero hz, div_eq_mul_inv, ← Real.exp_neg]
  have h : -(arg z * w.im) ≤ Real.pi * |w.im| := by
    calc -(arg z * w.im) ≤ |arg z * w.im| := neg_le_abs _
      _ = |arg z| * |w.im| := abs_mul _ _
      _ ≤ Real.pi * |w.im| := by
        gcongr
        exact Complex.abs_arg_le_pi z
  gcongr

lemma norm_factor (c : ℂ) (hc : c = I ∨ c = -I) (t : ℝ) :
    ‖(1 : ℂ) + c * t‖ = (1 + t ^ 2) ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow, Complex.norm_eq_sqrt_sq_add_sq]
  rcases hc with rfl | rfl <;> simp

lemma norm_KK_le (α β : ℂ) (t : ℝ) :
    ‖KK α β 1 t‖ ≤ (Real.exp (Real.pi * |α.im|) * Real.exp (Real.pi * |β.im|)) *
      (1 + t ^ 2) ^ (-(α + β).re / 2) := by
  have hp : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have ne1 : (1 : ℂ) + (-I) * t ≠ 0 := slitPlane_ne_zero (mem_slit _ (by simp) t)
  have ne2 : (1 : ℂ) + I * t ≠ 0 := slitPlane_ne_zero (mem_slit _ (by simp) t)
  have a1 := norm_cpow_le _ (-α) ne1
  have a2 := norm_cpow_le _ (-β) ne2
  rw [norm_factor _ (Or.inr rfl), ← Real.rpow_mul hp.le] at a1
  rw [norm_factor _ (Or.inl rfl), ← Real.rpow_mul hp.le] at a2
  simp only [neg_re, neg_im, abs_neg] at a1 a2
  rw [KK_one_eq, norm_mul]
  calc _ ≤ _ := mul_le_mul a1 a2 (norm_nonneg _) (by positivity)
    _ = _ := by
      have : -(α + β).re / 2 = 1 / 2 * -α.re + 1 / 2 * -β.re := by simp only [add_re]; ring
      rw [this, Real.rpow_add hp]
      ring

lemma integrable_KK (α β : ℂ) (h : 1 < (α + β).re) : Integrable fun t : ℝ => KK α β 1 t := by
  have h0 : Integrable fun t : ℝ => (1 + ‖t‖ ^ 2) ^ (-(α + β).re / 2) :=
    integrable_rpow_neg_one_add_norm_sq (by simpa using h)
  refine (h0.const_mul (Real.exp (Real.pi * |α.im|) * Real.exp (Real.pi * |β.im|))).mono'
    (continuous_KK α β).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  simpa using norm_KK_le α β t

lemma tendsto_KK (α β : ℂ) (h : 0 < (α + β).re) (l : Filter ℝ) (hl : Tendsto (fun t : ℝ => |t|) l atTop) :
    Tendsto (fun t : ℝ => KK α β 1 t) l (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => 1 + t ^ 2) l atTop := by
    refine tendsto_atTop_add_const_left _ _ ?_
    have := (tendsto_pow_atTop (α := ℝ) (n := 2) two_ne_zero).comp hl
    simpa [Function.comp_def] using this
  have h2 : Tendsto (fun t : ℝ => (1 + t ^ 2) ^ (-((α + β).re / 2))) l (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity)).comp h1
  have h3 := h2.const_mul (Real.exp (Real.pi * |α.im|) * Real.exp (Real.pi * |β.im|))
  rw [mul_zero] at h3
  refine squeeze_zero_norm (fun t => ?_) h3
  have := norm_KK_le α β t
  rwa [neg_div] at this

lemma norm_ee_neg (ξ t : ℝ) : ‖ee (-(ξ * t))‖ = 1 := by
  have : (2 * (Real.pi : ℂ) * I * (-((ξ : ℂ) * t))) = ((-(2 * Real.pi * ξ * t) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [ee, this, Complex.norm_exp_ofReal_mul_I]

lemma hasDerivAt_ee (ξ t : ℝ) :
    HasDerivAt (fun u : ℝ => ee (-(ξ * u))) (-(2 * Real.pi * I * ξ) * ee (-(ξ * t))) t := by
  have h1 : HasDerivAt (fun z : ℂ => (-(2 * Real.pi * I * ξ)) * z) (-(2 * Real.pi * I * ξ)) (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).const_mul (-(2 * (Real.pi : ℂ) * I * ξ))
  have h2 := h1.cexp.comp_ofReal
  have e : (fun u : ℝ => ee (-(ξ * u))) = fun u : ℝ => cexp ((-(2 * Real.pi * I * ξ)) * u) := by
    funext u
    simp only [ee]
    congr 1
    ring
  have e2 : ee (-(ξ * t)) = cexp ((-(2 * Real.pi * I * ξ)) * t) := by
    simp only [ee]
    congr 1
    ring
  rw [e, e2]
  exact h2.congr_deriv (by ring)

lemma continuous_ee (ξ : ℝ) : Continuous fun t : ℝ => ee (-(ξ * t)) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_ee ξ t).continuousAt

lemma integrable_KK_ee (α β : ℂ) (h : 1 < (α + β).re) (ξ : ℝ) :
    Integrable fun t : ℝ => KK α β 1 t * ee (-(ξ * t)) := by
  refine (integrable_KK α β h).norm.mono'
    ((continuous_KK α β).mul (continuous_ee ξ)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  simp [norm_ee_neg]

lemma Phi_ibp (α β : ℂ) (h : 1 < (α + β).re) (ξ : ℝ) :
    2 * Real.pi * ξ * Phi α β ξ = α * Phi (α + 1) β ξ - β * Phi α (β + 1) ξ := by
  have hα : 1 < (α + 1 + β).re := by simp only [add_re, one_re] at *; linarith
  have hβ : 1 < (α + (β + 1)).re := by simp only [add_re, one_re] at *; linarith
  have i1 := (integrable_KK_ee (α + 1) β hα ξ).const_mul (I * α)
  have i2 := (integrable_KK_ee α (β + 1) hβ ξ).const_mul (I * β)
  have i3 := (integrable_KK_ee α β h ξ).const_mul (2 * Real.pi * I * ξ)
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => KK α β 1 u * ee (-(ξ * u)))
      (I * α * (KK (α + 1) β 1 t * ee (-(ξ * t))) - I * β * (KK α (β + 1) 1 t * ee (-(ξ * t))) -
        2 * Real.pi * I * ξ * (KK α β 1 t * ee (-(ξ * t)))) t := by
    intro t
    refine HasDerivAt.congr_deriv (f := fun u : ℝ => KK α β 1 u * ee (-(ξ * u)))
      ((hasDerivAt_KK α β t).mul (hasDerivAt_ee ξ t)) ?_
    ring
  have tz : ∀ l : Filter ℝ, Tendsto (fun t : ℝ => |t|) l atTop →
      Tendsto (fun u : ℝ => KK α β 1 u * ee (-(ξ * u))) l (𝓝 0) := by
    intro l hl
    refine squeeze_zero_norm (fun t => ?_) (tendsto_zero_iff_norm_tendsto_zero.1
      (tendsto_KK α β (by linarith) l hl))
    simp [norm_ee_neg]
  have i12 : Integrable (fun t : ℝ => I * α * (KK (α + 1) β 1 t * ee (-(ξ * t))) -
      I * β * (KK α (β + 1) 1 t * ee (-(ξ * t)))) := i1.sub i2
  have key := integral_of_hasDerivAt_of_tendsto hd (i12.sub i3)
    (tz atBot tendsto_abs_atBot_atTop) (tz atTop tendsto_abs_atTop_atTop)
  rw [integral_sub i12 i3, integral_sub i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, sub_zero] at key
  have key' : I * α * Phi (α + 1) β ξ - I * β * Phi α (β + 1) ξ -
      2 * Real.pi * I * ξ * Phi α β ξ = 0 := key
  have : I * (2 * Real.pi * ξ * Phi α β ξ - (α * Phi (α + 1) β ξ - β * Phi α (β + 1) ξ)) = 0 := by
    linear_combination -key'
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 I_ne_zero
  · exact sub_eq_zero.1 h0

lemma KK_split (α β : ℂ) (t : ℝ) :
    2 * KK (α + 1) β 1 t = KK α β 1 t + KK (α + 1) (β - 1) 1 t := by
  have ne1 : (1 : ℂ) + (-I) * t ≠ 0 := slitPlane_ne_zero (mem_slit _ (by simp) t)
  have ne2 : (1 : ℂ) + I * t ≠ 0 := slitPlane_ne_zero (mem_slit _ (by simp) t)
  have e1 : ((1 : ℂ) + (-I) * t) ^ (-α) = ((1 : ℂ) + (-I) * t) ^ (-(α + 1)) * ((1 : ℂ) + (-I) * t) := by
    have : -α = -(α + 1) + 1 := by ring
    rw [this, cpow_add _ _ ne1, cpow_one]
  have e2 : ((1 : ℂ) + I * t) ^ (-(β - 1)) = ((1 : ℂ) + I * t) ^ (-β) * ((1 : ℂ) + I * t) := by
    have : -(β - 1) = -β + 1 := by ring
    rw [this, cpow_add _ _ ne2, cpow_one]
  rw [KK_one_eq, KK_one_eq, KK_one_eq, e1, e2]
  ring

lemma Phi_zero (α β : ℂ) (h : 1 < (α + β).re) :
    (α + β - 1) * Phi α β 0 = 2 * α * Phi (α + 1) β 0 := by
  have hα : 1 < (α + 1 + β).re := by simp only [add_re, one_re] at *; linarith
  have hm : 1 < (α + 1 + (β - 1)).re := by
    simp only [add_re, sub_re, one_re] at *; linarith
  have hz : 0 < (α + (β - 1)).re := by
    simp only [add_re, sub_re, one_re] at *; linarith
  have ee0 : ∀ t : ℝ, ee (-(((0 : ℝ) : ℂ) * t)) = 1 := by intro t; simp [ee]
  have P : ∀ a b : ℂ, Phi a b 0 = ∫ t : ℝ, KK a b 1 t := by
    intro a b
    simp only [Phi, ee0, mul_one]
  have i1 := (integrable_KK (α + 1) (β - 1) hm).const_mul (I * α)
  have i2 := (integrable_KK α β h).const_mul (I * (β - 1))
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => KK α (β - 1) 1 u)
      (I * α * KK (α + 1) (β - 1) 1 t - I * (β - 1) * KK α β 1 t) t := by
    intro t
    have := hasDerivAt_KK α (β - 1) t
    rwa [sub_add_cancel] at this
  have key := integral_of_hasDerivAt_of_tendsto hd (i1.sub i2)
    (tendsto_KK α (β - 1) hz atBot tendsto_abs_atBot_atTop)
    (tendsto_KK α (β - 1) hz atTop tendsto_abs_atTop_atTop)
  rw [integral_sub i1 i2, integral_const_mul, integral_const_mul, sub_zero, ← P, ← P] at key
  have two : 2 * Phi (α + 1) β 0 = Phi α β 0 + Phi (α + 1) (β - 1) 0 := by
    rw [P, P, P, ← integral_const_mul, ← integral_add (integrable_KK α β h)
      (integrable_KK (α + 1) (β - 1) hm)]
    exact integral_congr_ae (Eventually.of_forall fun t => KK_split α β t)
  have key2 : α * Phi (α + 1) (β - 1) 0 = (β - 1) * Phi α β 0 := by
    have : I * (α * Phi (α + 1) (β - 1) 0 - (β - 1) * Phi α β 0) = 0 := by
      linear_combination key
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 I_ne_zero
    · exact sub_eq_zero.1 h0
  linear_combination (-α) * two - key2

theorem kernel_fourier_integration_by_parts : W0 → W1 := fun _ α β h =>
  ⟨fun ξ => Phi_ibp α β h ξ, Phi_zero α β h⟩

end GlobalTheory.CompanionTheory.HalfIntegral

end
