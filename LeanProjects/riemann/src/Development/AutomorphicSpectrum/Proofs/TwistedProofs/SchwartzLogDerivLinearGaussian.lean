import Mathlib

namespace GlobalTheory.CompanionTheory.Twist

theorem schwartz_logDeriv_linear_formula {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f₀ : SchwartzMap V ℂ) (m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
    (hm : ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y) (y : V) :
    f₀ y = f₀ 0 * Complex.exp (m y y / 2) := by
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f₀ (s • y)) ((t : ℂ) * m y y * f₀ (t • y)) t := by
    intro t
    have h1 : HasFDerivAt f₀ (fderiv ℝ f₀ (t • y)) (t • y) := f₀.differentiableAt.hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => s • y) y t := by
      simpa using (hasDerivAt_id t).smul_const y
    have h3 : HasDerivAt (fun s : ℝ => f₀ (s • y)) (fderiv ℝ f₀ (t • y) y) t :=
      h1.comp_hasDerivAt t h2
    rw [hm, map_smul, Complex.real_smul] at h3
    exact h3
  have hE : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) ^ 2 * m y y / 2)))
      (Complex.exp (-((t : ℂ) ^ 2 * m y y / 2)) * (-((t : ℂ) * m y y))) t := by
    intro t
    have h5 : HasDerivAt (fun z : ℂ => -(z ^ 2 * m y y / 2)) (-((t : ℂ) * m y y)) (t : ℂ) := by
      have h6 := (((hasDerivAt_pow 2 (t : ℂ)).mul_const (m y y)).div_const 2).neg
      refine h6.congr_deriv ?_
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    exact h5.cexp.comp_ofReal
  have hH : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => f₀ (s • y) * Complex.exp (-((s : ℂ) ^ 2 * m y y / 2))) 0 t := by
    intro t
    refine ((hg t).mul (hE t)).congr_deriv ?_
    ring
  have h10 := is_const_of_deriv_eq_zero (fun t => (hH t).differentiableAt) (fun t => (hH t).deriv) 1 0
  simp only [one_smul, zero_smul, Complex.ofReal_one, Complex.ofReal_zero, one_pow, one_mul,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_div, neg_zero,
    Complex.exp_zero, mul_one] at h10
  calc f₀ y = f₀ y * Complex.exp (-(m y y / 2)) * Complex.exp (m y y / 2) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = f₀ 0 * Complex.exp (m y y / 2) := by rw [h10]

theorem schwartz_logDeriv_linear_gaussian {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (f₀ : SchwartzMap V ℂ) (hf : f₀ ≠ 0)
    (m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (hm : ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y) :
    ∃ (c₀ : ℂ) (Q Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), c₀ ≠ 0 ∧ (∀ x, x ≠ 0 → 0 < Q x x) ∧
      ∀ x, f₀ x = c₀ * Complex.exp (-(Q x x : ℂ) - Complex.I * (Q' x x : ℂ)) := by
  have hform := fun y => schwartz_logDeriv_linear_formula f₀ m hm y
  have hc0 : f₀ 0 ≠ 0 := by
    intro h0
    apply hf
    ext x
    simp [hform x, h0]
  refine ⟨f₀ 0, (-(1 / 2 : ℝ)) • m.compr₂ Complex.reLm, (-(1 / 2 : ℝ)) • m.compr₂ Complex.imLm,
    hc0, ?_, ?_⟩
  · intro x hx
    simp only [LinearMap.smul_apply, LinearMap.compr₂_apply, Complex.reLm_coe, smul_eq_mul]
    by_contra hle
    push Not at hle
    have hre : 0 ≤ (m x x).re := by linarith
    obtain ⟨C, hCpos, hC⟩ := f₀.decay 1 0
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hcpos : 0 < ‖f₀ 0‖ := norm_pos_iff.mpr hc0
    set t : ℝ := C / (‖f₀ 0‖ * ‖x‖) + 1 with ht
    have htpos : 0 < t := by positivity
    have hlow : ‖f₀ 0‖ ≤ ‖f₀ (t • x)‖ := by
      rw [hform (t • x), norm_mul, Complex.norm_exp]
      apply le_mul_of_one_le_right (norm_nonneg _)
      apply Real.one_le_exp
      simp only [map_smul, LinearMap.smul_apply, smul_smul, Complex.div_ofNat_re, Complex.smul_re,
        smul_eq_mul]
      have h6 := mul_nonneg (mul_self_nonneg t) hre
      linarith
    have hdec := hC (t • x)
    rw [pow_one, norm_iteratedFDeriv_zero, norm_smul, Real.norm_eq_abs, abs_of_pos htpos] at hdec
    have hbig : C < t * ‖x‖ * ‖f₀ 0‖ := by
      have hne : ‖f₀ 0‖ * ‖x‖ ≠ 0 := by positivity
      have heq : t * ‖x‖ * ‖f₀ 0‖ = C + ‖x‖ * ‖f₀ 0‖ := by
        rw [ht]
        field_simp
      rw [heq]
      linarith [mul_pos hxpos hcpos]
    have h7 : t * ‖x‖ * ‖f₀ 0‖ ≤ t * ‖x‖ * ‖f₀ (t • x)‖ :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    linarith
  · intro x
    rw [hform x]
    congr 1
    congr 1
    simp only [LinearMap.smul_apply, LinearMap.compr₂_apply, Complex.reLm_coe, Complex.imLm_coe,
      smul_eq_mul]
    apply Complex.ext <;> simp <;> ring

end GlobalTheory.CompanionTheory.Twist
