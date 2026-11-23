import Mathlib

namespace GroundTheory.Automorphic

open MeasureTheory Set Filter Topology Real Function
open scoped ContDiff FourierTransform

noncomputable section

namespace LineKernel

def cutoff (r t : ℝ) : ℝ := 1 - smoothTransition (t / r - 1)

theorem contDiff_cutoff (r : ℝ) {n : ℕ∞} : ContDiff ℝ n (cutoff r) := by
  unfold cutoff
  exact contDiff_const.sub (smoothTransition.contDiff.comp
    ((contDiff_id.div_const r).sub contDiff_const))

theorem cutoff_eq_one {r t : ℝ} (hr : 0 < r) (ht : t ≤ r) : cutoff r t = 1 := by
  unfold cutoff
  rw [smoothTransition.zero_of_nonpos, sub_zero]
  rw [sub_nonpos, div_le_one hr]; exact ht

theorem cutoff_eq_zero {r t : ℝ} (hr : 0 < r) (ht : 2 * r ≤ t) : cutoff r t = 0 := by
  unfold cutoff
  rw [smoothTransition.one_of_one_le, sub_self]
  rw [le_sub_iff_add_le, le_div_iff₀ hr]; linarith

theorem cutoff_nonneg (r t : ℝ) : 0 ≤ cutoff r t := by
  unfold cutoff; linarith [smoothTransition.le_one (t / r - 1)]

theorem cutoff_le_one (r t : ℝ) : cutoff r t ≤ 1 := by
  unfold cutoff; linarith [smoothTransition.nonneg (t / r - 1)]

theorem iteratedDeriv_deriv_cutoff_eq_zero {r t : ℝ} (hr : 0 < r) (ht : t ∉ Icc r (2 * r))
    (q : ℕ) : iteratedDeriv q (deriv (cutoff r)) t = 0 := by
  have hzero : deriv (cutoff r) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    rcases not_and_or.1 ht with h | h
    · push Not at h
      have hev : cutoff r =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [Iio_mem_nhds h] with s hs using cutoff_eq_one hr (le_of_lt hs)
      filter_upwards [Iio_mem_nhds h] with s hs
      have hev' : cutoff r =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
        filter_upwards [Iio_mem_nhds hs] with u hu using cutoff_eq_one hr (le_of_lt hu)
      rw [hev'.deriv_eq]; simp
    · push Not at h
      filter_upwards [Ioi_mem_nhds h] with s hs
      have hev' : cutoff r =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hs] with u hu using cutoff_eq_zero hr (le_of_lt hu)
      rw [hev'.deriv_eq]; simp
  rw [hzero.iteratedDeriv_eq]; simp

def kern (a r : ℝ) : ℝ → ℝ :=
  indicator (Ici 0) fun t => a * exp (-a * t) * cutoff r t

def rem (a r : ℝ) (t : ℝ) : ℝ := -(exp (-a * t) * deriv (cutoff r) t)

theorem kern_nonneg {a : ℝ} (ha : 0 ≤ a) (r t : ℝ) : 0 ≤ kern a r t := by
  unfold kern indicator
  split_ifs
  · exact mul_nonneg (mul_nonneg ha (exp_pos _).le) (cutoff_nonneg r t)
  · exact le_rfl

theorem kern_eq_zero_of_neg {a r t : ℝ} (ht : t < 0) : kern a r t = 0 := by
  unfold kern; rw [indicator_of_notMem]; exact fun h => absurd (mem_Ici.1 h) (not_le.2 ht)

theorem kern_eq_zero_of_ge {a r t : ℝ} (hr : 0 < r) (ht : 2 * r ≤ t) : kern a r t = 0 := by
  unfold kern indicator; split_ifs <;> simp [cutoff_eq_zero hr ht]

theorem kern_of_nonneg {a r t : ℝ} (ht : 0 ≤ t) : kern a r t = a * exp (-a * t) * cutoff r t := by
  unfold kern; rw [indicator_of_mem (mem_Ici.2 ht)]

theorem support_kern_subset {a r : ℝ} (hr : 0 < r) : support (kern a r) ⊆ Icc 0 (2 * r) := by
  intro t ht
  by_contra h
  rcases not_and_or.1 h with h | h
  · exact ht (kern_eq_zero_of_neg (not_le.1 h))
  · exact ht (kern_eq_zero_of_ge hr (not_le.1 h).le)

theorem kern_le {a : ℝ} (ha : 0 ≤ a) (r t : ℝ) : kern a r t ≤ a := by
  unfold kern indicator
  split_ifs with ht
  · have h1 : exp (-a * t) ≤ 1 := exp_le_one_iff.2 (by nlinarith [mem_Ici.1 ht])
    calc a * exp (-a * t) * cutoff r t ≤ a * 1 * 1 := by
          gcongr
          · exact cutoff_nonneg r t
          · exact cutoff_le_one r t
      _ = a := by ring
  · exact ha

theorem measurable_kern (a r : ℝ) : Measurable (kern a r) := by
  unfold kern
  exact (((continuous_const.mul (continuous_exp.comp (continuous_const.mul continuous_id))).mul
    (contDiff_cutoff r (n := 0)).continuous).measurable).indicator measurableSet_Ici

theorem integrable_kern {a : ℝ} (ha : 0 ≤ a) {r : ℝ} (hr : 0 < r) : Integrable (kern a r) := by
  have hon : IntegrableOn (kern a r) (Icc 0 (2 * r)) := by
    refine Measure.integrableOn_of_bounded (M := a) (measure_Icc_lt_top).ne
      (measurable_kern a r).aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (kern_nonneg ha r t)]; exact kern_le ha r t
  refine hon.integrable_of_forall_notMem_eq_zero fun t ht => ?_
  by_contra h; exact ht (support_kern_subset hr h)

theorem contDiff_deriv_cutoff (r : ℝ) : ContDiff ℝ ∞ (deriv (cutoff r)) :=
  (contDiff_infty_iff_deriv.1 (contDiff_cutoff r)).2

theorem contDiff_rem (a r : ℝ) : ContDiff ℝ ∞ (rem a r) := by
  unfold rem
  exact ((contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul (contDiff_deriv_cutoff r)).neg

theorem rem_eq_zero {a r t : ℝ} (hr : 0 < r) (ht : t ∉ Icc r (2 * r)) : rem a r t = 0 := by
  have := iteratedDeriv_deriv_cutoff_eq_zero hr ht 0
  simp only [iteratedDeriv_zero] at this
  simp [rem, this]

theorem support_rem_subset {a r : ℝ} (hr : 0 < r) : support (rem a r) ⊆ Icc r (2 * r) := by
  intro t ht; by_contra h; exact ht (rem_eq_zero hr h)

theorem hasCompactSupport_rem {a r : ℝ} (hr : 0 < r) : HasCompactSupport (rem a r) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_rem_subset hr)

theorem integral_eq_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} {b : ℝ} (hb : 0 ≤ b) (hg : ∀ t ∉ Icc 0 b, g t = 0) :
    ∫ t, g t = ∫ t in (0 : ℝ)..b, g t := by
  rw [intervalIntegral.integral_of_le hb, ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero hg]

theorem step_identity {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {F F' : ℝ → ℂ}
    (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F') :
    F 0 = (∫ t, (F t - (a : ℂ)⁻¹ * F' t) * (kern a r t : ℂ)) + ∫ t, F t * (rem a r t : ℂ) := by
  have hb : (0 : ℝ) ≤ 2 * r := by linarith
  have e1 : ∫ t, (F t - (a : ℂ)⁻¹ * F' t) * (kern a r t : ℂ) =
      ∫ t in (0 : ℝ)..2 * r, (F t - (a : ℂ)⁻¹ * F' t) * (kern a r t : ℂ) := by
    refine integral_eq_intervalIntegral hb fun t ht => ?_
    rcases not_and_or.1 ht with h | h
    · rw [kern_eq_zero_of_neg (not_le.1 h)]; simp
    · rw [kern_eq_zero_of_ge hr (not_le.1 h).le]; simp
  have e2 : ∫ t, F t * (rem a r t : ℂ) = ∫ t in (0 : ℝ)..2 * r, F t * (rem a r t : ℂ) := by
    refine integral_eq_intervalIntegral hb fun t ht => ?_
    rw [rem_eq_zero hr (fun h => ht ⟨hr.le.trans h.1, h.2⟩)]; simp
  suffices hsuff : F 0 = (∫ t in (0 : ℝ)..2 * r, (F t - (a : ℂ)⁻¹ * F' t) * (kern a r t : ℂ)) +
      ∫ t in (0 : ℝ)..2 * r, F t * (rem a r t : ℂ) by
    rw [hsuff, ← e1, ← e2]
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun t => (hF t).continuousAt
  set E : ℝ → ℝ := fun t => exp (-a * t) with hE
  set χ := cutoff r with hχ
  set χ' := deriv (cutoff r) with hχ'
  have hEd : ∀ t, HasDerivAt E (-a * E t) t := by
    intro t
    have := ((hasDerivAt_id t).const_mul (-a)).exp
    simpa [hE, mul_comm] using this
  have hχd : ∀ t, HasDerivAt χ (χ' t) t := fun t =>
    ((contDiff_cutoff r (n := 1)).differentiable one_ne_zero t).hasDerivAt
  have hEc : Continuous E := continuous_exp.comp (continuous_const.mul continuous_id)
  have hχc : Continuous χ := (contDiff_cutoff r (n := 0)).continuous
  have hχ'c : Continuous χ' := (contDiff_deriv_cutoff r).continuous
  set φ : ℝ → ℂ := fun t => F t * ((E t * χ t : ℝ) : ℂ) with hφ
  set φ' : ℝ → ℂ := fun t => F' t * ((E t * χ t : ℝ) : ℂ) +
    F t * ((-a * E t * χ t + E t * χ' t : ℝ) : ℂ) with hφ'
  have hφd : ∀ t, HasDerivAt φ (φ' t) t := by
    intro t
    have h1 : HasDerivAt (fun t => E t * χ t) (-a * E t * χ t + E t * χ' t) t := by
      exact (hEd t).mul (hχd t)
    exact (hF t).mul h1.ofReal_comp
  have hφ'c : Continuous φ' := by
    simp only [hφ']; fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * r)
    (fun t _ => hφd t) (hφ'c.intervalIntegrable _ _)
  have hc0 : cutoff r 0 = 1 := cutoff_eq_one hr hr.le
  have hφ0 : φ 0 = F 0 := by simp [hφ, hE, hχ, hc0]
  have hφ2 : φ (2 * r) = 0 := by simp [hφ, hχ, cutoff_eq_zero hr le_rfl]
  rw [hφ0, hφ2, zero_sub] at hFTC
  · rw [← intervalIntegral.integral_add]
    · have : ∫ t in (0 : ℝ)..2 * r, ((F t - (a : ℂ)⁻¹ * F' t) * (kern a r t : ℂ) +
          F t * (rem a r t : ℂ)) = ∫ t in (0 : ℝ)..2 * r, -φ' t := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hb] at ht
        simp only [hφ', kern_of_nonneg ht.1, rem, hE, hχ, hχ']
        have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
        push_cast
        field_simp
        ring
      rw [this, intervalIntegral.integral_neg, hFTC, neg_neg]
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hb]
      have : EqOn (fun t => (F t - (a : ℂ)⁻¹ * F' t) * (kern a r t : ℂ))
          (fun t => (F t - (a : ℂ)⁻¹ * F' t) * ((a * E t * χ t : ℝ) : ℂ)) (Icc 0 (2 * r)) := by
        intro t ht; simp only [kern_of_nonneg ht.1, hE, hχ]
      refine ContinuousOn.congr ?_ this
      exact Continuous.continuousOn (by fun_prop)
    · exact (Continuous.intervalIntegrable (by
        have : Continuous (rem a r) := (contDiff_rem a r).continuous
        fun_prop) _ _)

theorem antitone_cutoff {r : ℝ} (hr : 0 < r) : Antitone (cutoff r) := by
  intro s t hst
  unfold cutoff
  have : s / r - 1 ≤ t / r - 1 := by
    have := div_le_div_of_nonneg_right hst hr.le; linarith
  linarith [smoothTransition.monotone this]

theorem deriv_cutoff_nonpos {r : ℝ} (hr : 0 < r) (t : ℝ) : deriv (cutoff r) t ≤ 0 :=
  (antitone_cutoff hr).deriv_nonpos

theorem rem_nonneg {a r : ℝ} (hr : 0 < r) (t : ℝ) : 0 ≤ rem a r t := by
  unfold rem
  have := deriv_cutoff_nonpos hr t
  nlinarith [exp_pos (-a * t)]

theorem integrable_rem {a r : ℝ} (hr : 0 < r) : Integrable (rem a r) :=
  (contDiff_rem a r).continuous.integrable_of_hasCompactSupport (hasCompactSupport_rem hr)

theorem integral_deriv_cutoff {r : ℝ} (hr : 0 < r) : ∫ t, deriv (cutoff r) t = -1 := by
  have hb : (0 : ℝ) ≤ 2 * r := by linarith
  rw [integral_eq_intervalIntegral hb]
  · rw [intervalIntegral.integral_deriv_eq_sub (fun t _ =>
        ((contDiff_cutoff r (n := 1)).differentiable one_ne_zero t))
      ((contDiff_deriv_cutoff r).continuous.intervalIntegrable _ _),
      cutoff_eq_zero hr le_rfl, cutoff_eq_one hr hr.le]
    norm_num
  · intro t ht
    have := iteratedDeriv_deriv_cutoff_eq_zero hr (fun h => ht ⟨hr.le.trans h.1, h.2⟩) 0
    simpa using this

theorem integral_rem_le {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r) : ∫ t, rem a r t ≤ exp (-a * r) := by
  have hint : Integrable (deriv (cutoff r)) :=
    (contDiff_deriv_cutoff r).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun t ht => by
        by_contra h
        exact ht (by simpa using iteratedDeriv_deriv_cutoff_eq_zero hr h 0)))
  calc ∫ t, rem a r t ≤ ∫ t, exp (-a * r) * -deriv (cutoff r) t := by
        refine integral_mono (integrable_rem hr) (hint.neg.const_mul _) fun t => ?_
        by_cases ht : t ∈ Icc r (2 * r)
        · unfold rem
          have h1 : exp (-a * t) ≤ exp (-a * r) := exp_le_exp.2 (by nlinarith [ht.1])
          have h2 := deriv_cutoff_nonpos hr t
          nlinarith
        · rw [rem_eq_zero hr ht]
          have := iteratedDeriv_deriv_cutoff_eq_zero hr ht 0
          simp only [iteratedDeriv_zero] at this
          simp [this]
    _ = exp (-a * r) := by
        rw [integral_const_mul, integral_neg, integral_deriv_cutoff hr]; ring

theorem integral_kern_add_integral_rem {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ t, kern a r t) + ∫ t, rem a r t = 1 := by
  have h := step_identity ha hr (F := fun _ => (1 : ℂ)) (F' := fun _ => 0)
    (fun t => hasDerivAt_const t 1) continuous_const
  simp only [mul_zero, sub_zero, one_mul, integral_complex_ofReal] at h
  exact_mod_cast h.symm

theorem integral_kern_le_one {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : ∫ t, kern a r t ≤ 1 := by
  have h1 := integral_kern_add_integral_rem ha hr
  have h2 : 0 ≤ ∫ t, rem a r t := integral_nonneg (rem_nonneg hr)
  linarith

theorem one_sub_exp_le_integral_kern {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    1 - exp (-a * r) ≤ ∫ t, kern a r t := by
  have h1 := integral_kern_add_integral_rem ha hr
  have h2 := integral_rem_le ha.le hr
  linarith

def khat (a r : ℝ) (ξ : ℝ) : ℂ := 𝓕 (fun t => (kern a r t : ℂ)) ξ

theorem khat_eq (a r ξ : ℝ) :
    khat a r ξ = ∫ t, Complex.exp (↑(-2 * π * t * ξ) * Complex.I) * (kern a r t : ℂ) := by
  rw [khat, fourier_real_eq_integral_exp_smul]; rfl

theorem norm_khat_le_one {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (ξ : ℝ) : ‖khat a r ξ‖ ≤ 1 := by
  rw [khat_eq]
  refine (norm_integral_le_integral_norm _).trans ?_
  have : (fun t => ‖Complex.exp (↑(-2 * π * t * ξ) * Complex.I) * (kern a r t : ℂ)‖) =
      fun t => kern a r t := by
    funext t
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (kern_nonneg ha.le r t)]
  rw [this]; exact integral_kern_le_one ha hr

theorem abs_mul_norm_khat_le {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (ξ : ℝ) :
    |ξ| * ‖khat a r ξ‖ ≤ a / π := by
  set c : ℂ := ↑(-2 * π * ξ) * Complex.I with hc
  set F : ℝ → ℂ := fun t => Complex.exp (↑(-2 * π * t * ξ) * Complex.I) with hF
  have hFd : ∀ t, HasDerivAt F (F t * c) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => ((-2 * π * t * ξ : ℝ) : ℂ)) ((-2 * π * ξ : ℝ) : ℂ) t := by
      have := (((hasDerivAt_id t).const_mul (-2 * π)).mul_const ξ).ofReal_comp
      simpa using this
    exact (h1.mul_const Complex.I).cexp
  have hFc : Continuous F := by simp only [hF]; fun_prop
  have hstep := step_identity ha hr hFd (hFc.mul continuous_const)
  have hF0 : F 0 = 1 := by simp [hF]
  rw [hF0] at hstep
  have e1 : ∫ t, (F t - (a : ℂ)⁻¹ * (F t * c)) * (kern a r t : ℂ) =
      (1 - (a : ℂ)⁻¹ * c) * khat a r ξ := by
    rw [khat_eq, ← integral_const_mul]
    congr 1; funext t; simp only [hF]; ring
  rw [e1] at hstep
  have hrem : ‖∫ t, F t * (rem a r t : ℂ)‖ ≤ 1 := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have : (fun t => ‖F t * (rem a r t : ℂ)‖) = fun t => rem a r t := by
      funext t
      rw [norm_mul, hF, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (rem_nonneg hr t)]
    rw [this]
    exact (integral_rem_le ha.le hr).trans (exp_le_one_iff.2 (by nlinarith))
  have hkey : (1 - (a : ℂ)⁻¹ * c) * khat a r ξ = 1 - ∫ t, F t * (rem a r t : ℂ) := by
    linear_combination (-1 : ℂ) * hstep
  have hn : ‖(1 - (a : ℂ)⁻¹ * c) * khat a r ξ‖ ≤ 2 := by
    rw [hkey]; exact (norm_sub_le _ _).trans (by simp; linarith)
  have him : |2 * π * ξ / a| ≤ ‖1 - (a : ℂ)⁻¹ * c‖ := by
    refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
    simp only [hc, Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.inv_re,
      Complex.inv_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_ofReal]
    congr 1
    field_simp
    ring
  rw [norm_mul] at hn
  have hpos : 0 < 2 * π / a := by positivity
  have h3 : |2 * π * ξ / a| = 2 * π / a * |ξ| := by
    rw [show 2 * π * ξ / a = 2 * π / a * ξ by ring, abs_mul, abs_of_pos hpos]
  rw [h3] at him
  have h4 : 2 * π / a * (|ξ| * ‖khat a r ξ‖) ≤ 2 := by
    calc 2 * π / a * (|ξ| * ‖khat a r ξ‖) = (2 * π / a * |ξ|) * ‖khat a r ξ‖ := by ring
      _ ≤ ‖1 - (a : ℂ)⁻¹ * c‖ * ‖khat a r ξ‖ := by gcongr
      _ ≤ 2 := hn
  have := mul_le_mul_of_nonneg_left h4 (le_of_lt (by positivity : (0 : ℝ) < a / (2 * π)))
  have e : a / (2 * π) * (2 * π / a * (|ξ| * ‖khat a r ξ‖)) = |ξ| * ‖khat a r ξ‖ := by
    field_simp
  rw [e] at this
  calc |ξ| * ‖khat a r ξ‖ ≤ a / (2 * π) * 2 := this
    _ = a / π := by field_simp

theorem norm_khat_sub_one_le {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (ξ : ℝ) :
    ‖khat a r ξ - 1‖ ≤ 4 * π * r * |ξ| + exp (-a * r) := by
  have hk := integrable_kern ha.le hr
  have hkc : Integrable fun t => (kern a r t : ℂ) := hk.ofReal
  set F : ℝ → ℂ := fun t => Complex.exp (↑(-2 * π * t * ξ) * Complex.I) with hF
  have hFc : Continuous F := by simp only [hF]; fun_prop
  have hint1 : Integrable fun t => F t * (kern a r t : ℂ) := by
    refine hkc.bdd_mul (c := 1) hFc.aestronglyMeasurable ?_
    filter_upwards with t
    rw [show F t = Complex.exp (↑(-2 * π * t * ξ) * Complex.I) from rfl,
      Complex.norm_exp_ofReal_mul_I]
  have hsplit : khat a r ξ - 1 = (∫ t, (F t - 1) * (kern a r t : ℂ)) +
      (((∫ t, kern a r t) - 1 : ℝ) : ℂ) := by
    have hkF : khat a r ξ = ∫ t, F t * (kern a r t : ℂ) := khat_eq a r ξ
    have h2 : ∫ t, (F t - 1) * (kern a r t : ℂ) =
        (∫ t, F t * (kern a r t : ℂ)) - ∫ t, (kern a r t : ℂ) := by
      simp only [sub_mul, one_mul]; exact integral_sub hint1 hkc
    rw [hkF, h2, integral_complex_ofReal]
    push_cast; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ t, ‖(F t - 1) * (kern a r t : ℂ)‖ ≤ ∫ t, 4 * π * r * |ξ| * kern a r t := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
            (hk.const_mul _) (Eventually.of_forall fun t => ?_)
          dsimp only
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kern_nonneg ha.le r t)]
          by_cases ht : t ∈ Icc 0 (2 * r)
          · have h1 : ‖F t - 1‖ ≤ |-2 * π * t * ξ| := by
              have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -2 * π * t * ξ)
              simpa [hF, mul_comm] using this
            have h2 : |-2 * π * t * ξ| ≤ 4 * π * r * |ξ| := by
              rw [show -2 * π * t * ξ = -(2 * π * t) * ξ by ring, abs_mul, abs_neg,
                abs_of_nonneg (by nlinarith [ht.1, pi_pos] : (0:ℝ) ≤ 2 * π * t)]
              have := ht.2
              have : 2 * π * t ≤ 4 * π * r := by nlinarith [pi_pos]
              exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
            exact mul_le_mul_of_nonneg_right (h1.trans h2) (kern_nonneg ha.le r t)
          · have : kern a r t = 0 := by
              by_contra h; exact ht (support_kern_subset hr h)
            simp [this]
      _ ≤ 4 * π * r * |ξ| := by
          rw [integral_const_mul]
          have := integral_kern_le_one ha hr
          have : 0 ≤ 4 * π * r * |ξ| := by positivity
          nlinarith
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith [integral_kern_le_one ha hr])]
    linarith [one_sub_exp_le_integral_kern ha hr]

theorem hasCompactSupport_iteratedDeriv_deriv_cutoff {r : ℝ} (hr : 0 < r) (i : ℕ) :
    HasCompactSupport (iteratedDeriv i (deriv (cutoff r))) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc fun t ht => by
    by_contra h; exact ht (iteratedDeriv_deriv_cutoff_eq_zero hr h i)

theorem norm_iteratedDeriv_rem_le {r : ℝ} (hr : 0 < r) (q : ℕ) :
    ∃ S, 0 ≤ S ∧ ∀ a, 0 ≤ a → ∀ t,
      ‖iteratedDeriv q (rem a r) t‖ ≤ 2 ^ q * (1 + a) ^ q * exp (-a * r) * S := by
  have hb : ∀ i, ∃ C, ∀ t, ‖iteratedDeriv i (deriv (cutoff r)) t‖ ≤ C := fun i =>
    (hasCompactSupport_iteratedDeriv_deriv_cutoff hr i).exists_bound_of_continuous
      ((contDiff_deriv_cutoff r).continuous_iteratedDeriv i (by exact_mod_cast le_top))
  choose C hC using hb
  refine ⟨∑ i ∈ Finset.range (q + 1), |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
  intro a ha t
  have hE : ContDiff ℝ ∞ fun t : ℝ => exp (-a * t) :=
    contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hrem : rem a r = -fun t => exp (-a * t) * deriv (cutoff r) t := by
    funext t; rfl
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, hrem, iteratedFDeriv_neg_apply, norm_neg]
  refine (norm_iteratedFDeriv_mul_le hE (contDiff_deriv_cutoff r) t
    (by exact_mod_cast le_top)).trans ?_
  simp_rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul]
  have hS : ∀ i ∈ Finset.range (q + 1), |C i| ≤ ∑ i ∈ Finset.range (q + 1), |C i| := fun i hi =>
    Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) hi
  calc ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖(-a) ^ i * exp (-a * t)‖ *
        ‖iteratedDeriv (q - i) (deriv (cutoff r)) t‖
      ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
          ((1 + a) ^ q * exp (-a * r) * ∑ i ∈ Finset.range (q + 1), |C i|) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have hiq : i ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hqi : q - i ∈ Finset.range (q + 1) := Finset.mem_range.2 (by omega)
        by_cases ht : t ∈ Icc r (2 * r)
        · have h1 : ‖(-a) ^ i * exp (-a * t)‖ ≤ (1 + a) ^ q * exp (-a * r) := by
            rw [norm_mul, norm_pow, norm_neg, Real.norm_eq_abs, abs_of_nonneg ha,
              Real.norm_eq_abs, abs_of_pos (exp_pos _)]
            have h2 : a ^ i ≤ (1 + a) ^ q := (pow_le_pow_left₀ ha (by linarith) i).trans
              (pow_le_pow_right₀ (by linarith) hiq)
            have h3 : exp (-a * t) ≤ exp (-a * r) := exp_le_exp.2 (by nlinarith [ht.1])
            exact mul_le_mul h2 h3 (exp_pos _).le (by positivity)
          have h4 : ‖iteratedDeriv (q - i) (deriv (cutoff r)) t‖ ≤ ∑ i ∈ Finset.range (q + 1), |C i| :=
            (hC (q - i) t).trans ((le_abs_self _).trans (hS _ hqi))
          exact mul_le_mul h1 h4 (norm_nonneg _) (by positivity)
        · rw [iteratedDeriv_deriv_cutoff_eq_zero hr ht, norm_zero, mul_zero]
          have : 0 ≤ ∑ i ∈ Finset.range (q + 1), |C i| :=
            Finset.sum_nonneg fun i _ => abs_nonneg _
          positivity
    _ = 2 ^ q * (1 + a) ^ q * exp (-a * r) * ∑ i ∈ Finset.range (q + 1), |C i| := by
        rw [← Finset.sum_mul]
        have : ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) = 2 ^ q := by
          exact_mod_cast Nat.sum_range_choose q
        rw [this]; ring

theorem tendsto_pow_mul_exp_neg_mul {r : ℝ} (hr : 0 < r) (q : ℕ) :
    Tendsto (fun a : ℝ => (1 + a) ^ q * exp (-a * r)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun a : ℝ => (1 + a) * r) atTop atTop :=
    (tendsto_atTop_add_const_left _ 1 tendsto_id).atTop_mul_const hr
  have h2 := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero q).comp h1).const_mul (exp r / r ^ q)
  rw [mul_zero] at h2
  refine h2.congr fun a => ?_
  simp only [Function.comp_apply]
  rw [mul_pow, show -((1 + a) * r) = -a * r + -r by ring, exp_add, exp_neg]
  field_simp

theorem eventually_norm_iteratedDeriv_rem_le {r : ℝ} (hr : 0 < r) (q : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ a in atTop, ∀ t, ‖iteratedDeriv q (rem a r) t‖ ≤ δ := by
  obtain ⟨S, hS0, hS⟩ := norm_iteratedDeriv_rem_le hr q
  have ht : Tendsto (fun a : ℝ => 2 ^ q * ((1 + a) ^ q * exp (-a * r)) * S) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_mul_exp_neg_mul hr q).const_mul (2 ^ q)).mul_const S
  filter_upwards [ht.eventually (ge_mem_nhds hδ), eventually_ge_atTop 0] with a ha ha0 t
  refine (hS a ha0 t).trans ?_
  calc 2 ^ q * (1 + a) ^ q * exp (-a * r) * S = 2 ^ q * ((1 + a) ^ q * exp (-a * r)) * S := by ring
    _ ≤ δ := ha

end LineKernel

end

end GroundTheory.Automorphic
