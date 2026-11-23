import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.PerronKernel

lemma ne_zero_of_re {σ t : ℝ} (h : σ ≠ 0) : (σ : ℂ) + t * I ≠ 0 := by
  intro h0
  apply h
  simpa using congrArg Complex.re h0

lemma ne_zero_of_im {σ t : ℝ} (h : t ≠ 0) : (σ : ℂ) + t * I ≠ 0 := by
  intro h0
  apply h
  simpa using congrArg Complex.im h0

lemma cont_vinv {σ : ℝ} (h : σ ≠ 0) : Continuous fun t : ℝ => ((σ : ℂ) + t * I)⁻¹ := by
  exact (by fun_prop : Continuous fun t : ℝ => (σ : ℂ) + t * I).inv₀ fun t => ne_zero_of_re h

lemma cont_hinv {t : ℝ} (h : t ≠ 0) : Continuous fun σ : ℝ => ((σ : ℂ) + t * I)⁻¹ := by
  exact (by fun_prop : Continuous fun σ : ℝ => (σ : ℂ) + t * I).inv₀ fun σ => ne_zero_of_im h

private lemma hasDerivAt_half_log_sub_I_mul_arctan_eq_inv {s : ℝ} (hs : s ≠ 0) (x : ℝ) :
    HasDerivAt (fun x : ℝ => ((Real.log (x ^ 2 + s ^ 2) / 2 : ℝ) : ℂ) - I * (Real.arctan (x / s) : ℂ))
      ((x : ℂ) + s * I)⁻¹ x := by
  have hpos : 0 < x ^ 2 + s ^ 2 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 + s ^ 2) / 2) (x / (x ^ 2 + s ^ 2)) x :=
    ((((hasDerivAt_pow 2 x).add_const (s ^ 2)).log hpos.ne').div_const 2).congr_deriv
      (by field_simp; ring)
  have h2a : HasDerivAt (fun y : ℝ => y / s) (1 / s) x := (hasDerivAt_id' x).div_const s
  have h2b := (Real.hasDerivAt_arctan (x / s)).comp x h2a
  have h2 : HasDerivAt (fun x : ℝ => Real.arctan (x / s)) (s / (x ^ 2 + s ^ 2)) x :=
    h2b.congr_deriv (by field_simp; ring)
  refine (h1.ofReal_comp.sub (h2.ofReal_comp.const_mul I)).congr_deriv ?_
  have hz : (x : ℂ) + s * I ≠ 0 := ne_zero_of_im hs
  have hc : (x : ℂ) ^ 2 + (s : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hpos.ne'
  symm
  apply inv_eq_of_mul_eq_one_right
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

lemma vinv {σ : ℝ} (h : σ ≠ 0) (T : ℝ) :
    ∫ t in (-T)..T, ((σ : ℂ) + t * I)⁻¹ = ((2 * Real.arctan (T / σ) : ℝ) : ℂ) := by
  have hs : -σ ≠ 0 := neg_ne_zero.mpr h
  have hd : ∀ t ∈ Set.uIcc (-T) T, HasDerivAt
      (fun t : ℝ => -I * (((Real.log (t ^ 2 + (-σ) ^ 2) / 2 : ℝ) : ℂ) -
        I * (Real.arctan (t / -σ) : ℂ))) ((σ : ℂ) + t * I)⁻¹ t := by
    intro t _
    refine ((hasDerivAt_half_log_sub_I_mul_arctan_eq_inv hs t).const_mul (-I)).congr_deriv ?_
    rw [show (t : ℂ) + ((-σ : ℝ) : ℂ) * I = -I * ((σ : ℂ) + t * I) by
      push_cast; ring_nf; rw [I_sq]; ring]
    rw [mul_inv, ← mul_assoc]
    rw [show -I * (-I)⁻¹ = 1 from mul_inv_cancel₀ (neg_ne_zero.mpr I_ne_zero), one_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((cont_vinv h).intervalIntegrable _ _)]
  simp only [neg_sq, neg_div, div_neg, neg_neg, Real.arctan_neg]
  push_cast
  ring_nf
  rw [I_sq]
  ring

lemma hinv {T : ℝ} (h : T ≠ 0) (a b : ℝ) :
    (∫ x in a..b, ((x : ℂ) + ((-T : ℝ) : ℂ) * I)⁻¹) - ∫ x in a..b, ((x : ℂ) + T * I)⁻¹
      = 2 * I * ((Real.arctan (b / T) - Real.arctan (a / T) : ℝ) : ℂ) := by
  have hs : -T ≠ 0 := neg_ne_zero.mpr h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_half_log_sub_I_mul_arctan_eq_inv hs x)
      ((cont_hinv hs).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_half_log_sub_I_mul_arctan_eq_inv h x)
      ((cont_hinv h).intervalIntegrable _ _)]
  simp only [neg_sq, div_neg, Real.arctan_neg]
  push_cast
  ring

lemma norm_exp (L σ t : ℝ) : ‖cexp (L * ((σ : ℂ) + t * I))‖ = Real.exp (L * σ) := by
  rw [Complex.norm_exp]
  simp

lemma vbound (L : ℝ) {σ T : ℝ} (h : σ ≠ 0) (hT : 0 ≤ T) :
    ‖∫ t in (-T)..T, cexp (L * ((σ : ℂ) + t * I)) / ((σ : ℂ) + t * I)‖
      ≤ Real.exp (L * σ) / |σ| * (2 * T) := by
  have hb : ∀ t ∈ Set.uIoc (-T) T,
      ‖cexp (L * ((σ : ℂ) + t * I)) / ((σ : ℂ) + t * I)‖ ≤ Real.exp (L * σ) / |σ| := by
    intro t _
    rw [norm_div, norm_exp]
    apply div_le_div_of_nonneg_left (Real.exp_pos _).le (abs_pos.mpr h)
    simpa using Complex.abs_re_le_norm ((σ : ℂ) + t * I)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rwa [show |T - -T| = 2 * T by rw [sub_neg_eq_add, ← two_mul, abs_of_nonneg (by linarith)]] at this

lemma hbound {L : ℝ} (hL : L ≠ 0) {t a b : ℝ} (h : t ≠ 0) (hab : a ≤ b) :
    ‖∫ x in a..b, cexp (L * ((x : ℂ) + t * I)) / ((x : ℂ) + t * I)‖
      ≤ (Real.exp (L * b) - Real.exp (L * a)) / (L * |t|) := by
  have hb : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.Ioc a b →
      ‖cexp (L * ((x : ℂ) + t * I)) / ((x : ℂ) + t * I)‖ ≤ Real.exp (L * x) / |t| := by
    refine Filter.Eventually.of_forall fun x _ => ?_
    rw [norm_div, norm_exp]
    apply div_le_div_of_nonneg_left (Real.exp_pos _).le (abs_pos.mpr h)
    simpa using Complex.abs_im_le_norm ((x : ℂ) + t * I)
  have hF : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => Real.exp (L * x) / (L * |t|))
      (Real.exp (L * x) / |t|) x := by
    intro x _
    refine (((hasDerivAt_id' x).const_mul L).exp.div_const (L * |t|)).congr_deriv ?_
    have ht : |t| ≠ 0 := abs_ne_zero.mpr h
    field_simp
  calc _ ≤ ∫ x in a..b, Real.exp (L * x) / |t| :=
        intervalIntegral.norm_integral_le_of_norm_le hab hb
          ((by fun_prop : Continuous fun x : ℝ => Real.exp (L * x) / |t|).intervalIntegrable _ _)
    _ = _ := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
          ((by fun_prop : Continuous fun x : ℝ => Real.exp (L * x) / |t|).intervalIntegrable _ _)]
        ring

lemma rect_right (L : ℝ) {a b : ℝ} (T : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, cexp (L * ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) / ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
    - (∫ x in a..b, cexp (L * ((x : ℂ) + T * I)) / ((x : ℂ) + T * I))
    + I * (∫ t in (-T)..T, cexp (L * ((b : ℂ) + t * I)) / ((b : ℂ) + t * I))
    - I * (∫ t in (-T)..T, cexp (L * ((a : ℂ) + t * I)) / ((a : ℂ) + t * I)) = 0 := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => cexp (L * z) / z)
      (Set.uIcc ((a : ℂ) + ((-T : ℝ) : ℂ) * I).re ((b : ℂ) + T * I).re ×ℂ
        Set.uIcc ((a : ℂ) + ((-T : ℝ) : ℂ) * I).im ((b : ℂ) + T * I).im) := by
    rintro z ⟨hzr, -⟩
    have hre : a ≤ z.re := by
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero,
        add_zero] at hzr
      rcases Set.mem_uIcc.mp hzr with h | h <;> linarith [h.1, h.2]
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div (by fun_prop) differentiableAt_id
    intro h0
    rw [h0, zero_re] at hre
    linarith
  have h1 : ((a : ℂ) + ((-T : ℝ) : ℂ) * I).re = a := by simp
  have h2 : ((a : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
  have h3 : ((b : ℂ) + (T : ℂ) * I).re = b := by simp
  have h4 : ((b : ℂ) + (T : ℂ) * I).im = T := by simp
  have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fun z : ℂ => cexp (L * z) / z) ((a : ℂ) + ((-T : ℝ) : ℂ) * I) ((b : ℂ) + T * I) hd
  rw [h1, h2, h3, h4] at this
  simpa only [smul_eq_mul] using this

lemma rect_left (L : ℝ) {a b T : ℝ} (ha : a < 0) (hb : 0 < b) (hT : 0 < T) :
    (∫ x in a..b, cexp (L * ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) / ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
    - (∫ x in a..b, cexp (L * ((x : ℂ) + T * I)) / ((x : ℂ) + T * I))
    + I * (∫ t in (-T)..T, cexp (L * ((b : ℂ) + t * I)) / ((b : ℂ) + t * I))
    - I * (∫ t in (-T)..T, cexp (L * ((a : ℂ) + t * I)) / ((a : ℂ) + t * I))
      = 2 * Real.pi * I := by
  set D : ℂ → ℂ := dslope (fun z : ℂ => cexp (L * z)) 0 with hD
  have hDd : Differentiable ℂ D := by
    have : DifferentiableOn ℂ D Set.univ :=
      (differentiableOn_dslope Filter.univ_mem).2 (by fun_prop)
    exact fun z => (this z trivial).differentiableAt Filter.univ_mem
  have hsplit : ∀ z : ℂ, z ≠ 0 → cexp (L * z) / z = D z + z⁻¹ := by
    intro z hz
    rw [hD, dslope_of_ne _ hz, slope_def_field]
    simp only [mul_zero, Complex.exp_zero, sub_zero]
    field_simp
    ring
  have hTn : -T ≠ 0 := by linarith
  have ha0 : a ≠ 0 := ha.ne
  have hb0 : b ≠ 0 := hb.ne'
  have hDc : Continuous D := hDd.continuous
  have sb : (∫ x in a..b, cexp (L * ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) / ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
      = (∫ x in a..b, D ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) + ∫ x in a..b, ((x : ℂ) + ((-T : ℝ) : ℂ) * I)⁻¹ := by
    have i1 : IntervalIntegrable (fun x : ℝ => D ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) MeasureTheory.volume a b :=
      (hDc.comp (by fun_prop : Continuous fun x : ℝ => ((x : ℂ) + ((-T : ℝ) : ℂ) * I))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add i1 ((cont_hinv hTn).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun x _ => hsplit _ (ne_zero_of_im hTn)
  have st : (∫ x in a..b, cexp (L * ((x : ℂ) + T * I)) / ((x : ℂ) + T * I))
      = (∫ x in a..b, D ((x : ℂ) + T * I)) + ∫ x in a..b, ((x : ℂ) + T * I)⁻¹ := by
    have i1 : IntervalIntegrable (fun x : ℝ => D ((x : ℂ) + T * I)) MeasureTheory.volume a b :=
      (hDc.comp (by fun_prop : Continuous fun x : ℝ => ((x : ℂ) + T * I))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add i1 ((cont_hinv hT.ne').intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun x _ => hsplit _ (ne_zero_of_im hT.ne')
  have sr : (∫ t in (-T)..T, cexp (L * ((b : ℂ) + t * I)) / ((b : ℂ) + t * I))
      = (∫ t in (-T)..T, D ((b : ℂ) + t * I)) + ∫ t in (-T)..T, ((b : ℂ) + t * I)⁻¹ := by
    have i1 : IntervalIntegrable (fun t : ℝ => D ((b : ℂ) + t * I)) MeasureTheory.volume (-T) T :=
      (hDc.comp (by fun_prop : Continuous fun t : ℝ => ((b : ℂ) + t * I))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add i1 ((cont_vinv hb0).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun t _ => hsplit _ (ne_zero_of_re hb0)
  have sl : (∫ t in (-T)..T, cexp (L * ((a : ℂ) + t * I)) / ((a : ℂ) + t * I))
      = (∫ t in (-T)..T, D ((a : ℂ) + t * I)) + ∫ t in (-T)..T, ((a : ℂ) + t * I)⁻¹ := by
    have i1 : IntervalIntegrable (fun t : ℝ => D ((a : ℂ) + t * I)) MeasureTheory.volume (-T) T :=
      (hDc.comp (by fun_prop : Continuous fun t : ℝ => ((a : ℂ) + t * I))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add i1 ((cont_vinv ha0).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun t _ => hsplit _ (ne_zero_of_re ha0)
  have h1 : ((a : ℂ) + ((-T : ℝ) : ℂ) * I).re = a := by simp
  have h2 : ((a : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
  have h3 : ((b : ℂ) + (T : ℂ) * I).re = b := by simp
  have h4 : ((b : ℂ) + (T : ℂ) * I).im = T := by simp
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    D ((a : ℂ) + ((-T : ℝ) : ℂ) * I) ((b : ℂ) + T * I) hDd.differentiableOn
  rw [h1, h2, h3, h4] at hrect
  simp only [smul_eq_mul] at hrect
  have e1 := hinv hT.ne' a b
  have e2 := vinv hb0 T
  have e3 := vinv ha0 T
  have r2 : Real.arctan (T / b) = Real.pi / 2 - Real.arctan (b / T) := by
    rw [← inv_div, Real.arctan_inv_of_pos (div_pos hb hT)]
  have r3 : Real.arctan (T / a) = -(Real.pi / 2) - Real.arctan (a / T) := by
    rw [← inv_div, Real.arctan_inv_of_neg (div_neg_of_neg_of_pos ha hT)]
  rw [r2] at e2
  rw [r3] at e3
  rw [sb, st, sr, sl]
  linear_combination (norm := skip) hrect + e1 + I * e2 - I * e3
  push_cast
  ring

lemma le_of_forall_large {x B K c : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (h : ∀ U : ℝ, c ≤ U → x ≤ B + K / U) : x ≤ B := by
  have h0 : Filter.Tendsto (fun U : ℝ => K / U) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have hlim := h0.const_add B
  rw [add_zero] at hlim
  exact ge_of_tendsto hlim ((Filter.eventually_ge_atTop c).mono fun U hU => h U hU)

lemma norm_le_three {x p q r : ℂ} (h : I * x = p - q + I * r ∨ I * x = q - p + I * r) :
    ‖x‖ ≤ ‖p‖ + ‖q‖ + ‖r‖ := by
  have hx : ‖x‖ = ‖I * x‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hr : ‖I * r‖ = ‖r‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  rcases h with h | h
  · rw [hx, h]
    calc ‖p - q + I * r‖ ≤ ‖p - q‖ + ‖I * r‖ := norm_add_le _ _
      _ ≤ ‖p‖ + ‖q‖ + ‖r‖ := by rw [hr]; linarith [norm_sub_le p q]
  · rw [hx, h]
    calc ‖q - p + I * r‖ ≤ ‖q - p‖ + ‖I * r‖ := norm_add_le _ _
      _ ≤ ‖p‖ + ‖q‖ + ‖r‖ := by rw [hr]; linarith [norm_sub_le q p]

lemma far_neg {L c T : ℝ} (hL : L < 0) (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I)‖
      ≤ 2 * Real.exp (L * c) / (T * |L|) := by
  apply le_of_forall_large (c := c) hc (K := 2 * T * Real.exp (L * c)) (by positivity)
  intro U hU
  have hU0 : 0 < U := lt_of_lt_of_le hc hU
  have hR := rect_right L T hc hU
  have h3 := norm_le_three
    (x := ∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I))
    (p := ∫ x in c..U, cexp (L * ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) / ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
    (q := ∫ x in c..U, cexp (L * ((x : ℂ) + T * I)) / ((x : ℂ) + T * I))
    (r := ∫ t in (-T)..T, cexp (L * ((U : ℂ) + t * I)) / ((U : ℂ) + t * I)) (Or.inl (by linear_combination -hR))
  have hLT : 0 < T * -L := mul_pos hT (neg_pos.mpr hL)
  have key : ∀ s : ℝ, |s| = T → (Real.exp (L * U) - Real.exp (L * c)) / (L * |s|)
      ≤ Real.exp (L * c) / (T * |L|) := by
    intro s hs
    rw [hs, abs_of_neg hL, show L * T = -(T * -L) by ring, div_neg, ← neg_div, neg_sub]
    exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (L * U)]) hLT.le
  have hp := (hbound hL.ne (t := -T) (neg_ne_zero.mpr hT.ne') hU).trans
    (key (-T) (by rw [abs_neg, abs_of_pos hT]))
  have hq := (hbound hL.ne (t := T) hT.ne' hU).trans (key T (abs_of_pos hT))
  have hexp : Real.exp (L * U) ≤ Real.exp (L * c) := Real.exp_le_exp.mpr (by nlinarith)
  have hr : Real.exp (L * U) / |U| * (2 * T) ≤ 2 * T * Real.exp (L * c) / U := by
    rw [abs_of_pos hU0, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hU0.le
  have hr' := (vbound L (σ := U) hU0.ne' hT.le).trans hr
  have h2 : 2 * Real.exp (L * c) / (T * |L|) =
      Real.exp (L * c) / (T * |L|) + Real.exp (L * c) / (T * |L|) := by ring
  rw [h2]
  linarith

lemma far_pos {L c T : ℝ} (hL : 0 < L) (hc : 0 < c) (hT : 0 < T) :
    ‖(∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I)) - 2 * Real.pi‖
      ≤ 2 * Real.exp (L * c) / (T * |L|) := by
  apply le_of_forall_large (c := c) hc (K := 2 * T) (by positivity)
  intro U hU
  have hU0 : 0 < U := lt_of_lt_of_le hc hU
  have hR := rect_left L (a := -U) (b := c) (T := T) (by linarith) hc hT
  have h3 := norm_le_three
    (x := (∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I)) - 2 * Real.pi)
    (p := ∫ x in (-U)..c, cexp (L * ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) / ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
    (q := ∫ x in (-U)..c, cexp (L * ((x : ℂ) + T * I)) / ((x : ℂ) + T * I))
    (r := ∫ t in (-T)..T, cexp (L * (((-U : ℝ) : ℂ) + t * I)) / (((-U : ℝ) : ℂ) + t * I)) (Or.inr (by linear_combination hR))
  have hLT : 0 < L * T := mul_pos hL hT
  have key : ∀ s : ℝ, |s| = T → (Real.exp (L * c) - Real.exp (L * -U)) / (L * |s|)
      ≤ Real.exp (L * c) / (T * |L|) := by
    intro s hs
    rw [hs, abs_of_pos hL, mul_comm T L]
    exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (L * -U)]) hLT.le
  have hUc : -U ≤ c := by linarith
  have hp := (hbound hL.ne' (t := -T) (neg_ne_zero.mpr hT.ne') hUc).trans
    (key (-T) (by rw [abs_neg, abs_of_pos hT]))
  have hq := (hbound hL.ne' (t := T) hT.ne' hUc).trans (key T (abs_of_pos hT))
  have hexp : Real.exp (L * -U) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hr : Real.exp (L * -U) / |-U| * (2 * T) ≤ 2 * T / U := by
    rw [abs_neg, abs_of_pos hU0, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hU0.le
  have hr' := (vbound L (σ := -U) (by linarith) hT.le).trans hr
  have h2 : 2 * Real.exp (L * c) / (T * |L|) =
      Real.exp (L * c) / (T * |L|) + Real.exp (L * c) / (T * |L|) := by ring
  rw [h2]
  linarith

lemma near (L : ℝ) {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I)‖
      ≤ Real.exp (L * c) * (Real.pi + 2 * (T * |L|)) := by
  have hc0 : c ≠ 0 := hc.ne'
  set g : ℝ → ℂ := fun t => (cexp (I * ((L * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I) with hg
  have hpt : ∀ t : ℝ, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I)
      = (Real.exp (L * c) : ℂ) * (g t + ((c : ℂ) + t * I)⁻¹) := by
    intro t
    have hz : (c : ℂ) + t * I ≠ 0 := ne_zero_of_re hc0
    have he : cexp (L * ((c : ℂ) + t * I)) =
        (Real.exp (L * c) : ℂ) * cexp (I * ((L * t : ℝ) : ℂ)) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [hg]
    rw [he]
    field_simp
    ring
  have hgc : Continuous g := by
    simp only [hg]
    exact (by fun_prop : Continuous fun t : ℝ => cexp (I * ((L * t : ℝ) : ℂ)) - 1).div
      (by fun_prop) fun t => ne_zero_of_re hc0
  have hgb : ∀ t ∈ Set.uIoc (-T) T, ‖g t‖ ≤ |L| := by
    intro t _
    have hz : (c : ℂ) + t * I ≠ 0 := ne_zero_of_re hc0
    have hzn : 0 < ‖(c : ℂ) + t * I‖ := norm_pos_iff.mpr hz
    simp only [hg]
    rw [norm_div, div_le_iff₀ hzn]
    calc ‖cexp (I * ((L * t : ℝ) : ℂ)) - 1‖ ≤ ‖L * t‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      _ = |L| * |t| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |L| * ‖(c : ℂ) + t * I‖ := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg L)
        simpa using Complex.abs_im_le_norm ((c : ℂ) + t * I)
  have hint : (∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I))
      = (Real.exp (L * c) : ℂ) *
        ((∫ t in (-T)..T, g t) + ∫ t in (-T)..T, ((c : ℂ) + t * I)⁻¹) := by
    rw [intervalIntegral.integral_congr (fun t _ => hpt t), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hgc.intervalIntegrable _ _)
        ((cont_vinv hc0).intervalIntegrable _ _)]
  rw [hint, vinv hc0 T, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hg2 := intervalIntegral.norm_integral_le_of_norm_le_const hgb
  rw [show |T - -T| = 2 * T by rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by linarith)]] at hg2
  have hat : |2 * Real.arctan (T / c)| ≤ Real.pi := by
    rw [abs_of_pos (by have := Real.arctan_pos.mpr (div_pos hT hc); linarith)]
    linarith [Real.arctan_lt_pi_div_two (T / c)]
  calc ‖(∫ t in (-T)..T, g t) + ((2 * Real.arctan (T / c) : ℝ) : ℂ)‖
      ≤ ‖∫ t in (-T)..T, g t‖ + ‖((2 * Real.arctan (T / c) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ |L| * (2 * T) + Real.pi := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        linarith
    _ = Real.pi + 2 * (T * |L|) := by ring

theorem truncated_perron_kernel : ∃ C : ℝ, 0 < C ∧ ∀ y c T : ℝ, 0 < y → y ≠ 1 → 0 < c → 1 ≤ T → ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) - (if 1 < y then 1 else 0)‖ ≤ C * y ^ c * min 1 (1 / (T * |Real.log y|)) := by
  refine ⟨3, by norm_num, fun y c T hy hy1 hc hT => ?_⟩
  have hint : (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      = ∫ t in (-T)..T, cexp ((Real.log y : ℝ) * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), Complex.ofReal_log hy.le]
  rw [hint, Real.rpow_def_of_pos hy]
  set L := Real.log y with hLdef
  set V := ∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I) with hV
  have hL : L ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy hy1
  have hT0 : 0 < T := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hE : 0 < Real.exp (L * c) := Real.exp_pos _
  have hLa : 0 < |L| := abs_pos.mpr hL
  have hTL : 0 < T * |L| := mul_pos hT0 hLa
  have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hfar : ‖(1 / (2 * Real.pi) : ℂ) * V - (if 1 < y then 1 else 0)‖
      ≤ 1 / (2 * Real.pi) * (2 * Real.exp (L * c) / (T * |L|)) := by
    split_ifs with h1
    · have hLp : 0 < L := Real.log_pos h1
      have e : (1 / (2 * Real.pi) : ℂ) * V - 1 = (1 / (2 * Real.pi) : ℂ) * (V - 2 * Real.pi) := by
        have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
        field_simp
      rw [e, norm_mul, hn]
      exact mul_le_mul_of_nonneg_left (far_pos hLp hc hT0) (by positivity)
    · have hLn : L < 0 := Real.log_neg hy (lt_of_le_of_ne (not_lt.mp h1) hy1)
      rw [sub_zero, norm_mul, hn]
      exact mul_le_mul_of_nonneg_left (far_neg hLn hc hT0) (by positivity)
  have hind : ‖(if 1 < y then (1 : ℂ) else 0)‖ ≤ Real.exp (L * c) := by
    split_ifs with h1
    · rw [norm_one]
      exact Real.one_le_exp (mul_nonneg (Real.log_pos h1).le hc.le)
    · rw [norm_zero]
      exact hE.le
  have hnr : ‖(1 / (2 * Real.pi) : ℂ) * V - (if 1 < y then 1 else 0)‖
      ≤ 1 / (2 * Real.pi) * (Real.exp (L * c) * (Real.pi + 2 * (T * |L|))) + Real.exp (L * c) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, hn]
    exact add_le_add (mul_le_mul_of_nonneg_left (near L hc hT0) (by positivity)) hind
  rcases le_or_gt (T * |L|) 1 with hs | hs
  · rw [min_eq_left (by rw [le_div_iff₀ hTL]; linarith)]
    refine hnr.trans ?_
    have h2 : 1 / (2 * Real.pi) * (Real.exp (L * c) * (Real.pi + 2 * (T * |L|)))
        ≤ Real.exp (L * c) * 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hs hE.le, Real.pi_gt_three]
    linarith
  · rw [min_eq_right (by rw [div_le_iff₀ hTL]; linarith)]
    refine hfar.trans ?_
    rw [show 1 / (2 * Real.pi) * (2 * Real.exp (L * c) / (T * |L|))
        = 1 / Real.pi * (Real.exp (L * c) / (T * |L|)) by field_simp,
      show 3 * Real.exp (L * c) * (1 / (T * |L|)) = 3 * (Real.exp (L * c) / (T * |L|)) by ring]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ hpi]
    nlinarith [Real.pi_gt_three]

end GlobalTheory.PerronKernel
