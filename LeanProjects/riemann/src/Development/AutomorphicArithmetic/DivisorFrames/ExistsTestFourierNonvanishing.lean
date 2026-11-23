import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
import Development.AutomorphicArithmetic.DivisorFrames.GaussianFourierConjPower
open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

private lemma rad_int (p : ℝ) (hp : -2 < p) :
    Integrable (fun s : ℂ => ‖s‖ ^ p * Real.exp (-Real.pi * ‖s‖ ^ 2)) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun r : ℝ => r ^ p * Real.exp (-Real.pi * r ^ 2))]
  have h := integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := p + 1) (by linarith)
  refine h.congr_fun (fun r hr => ?_) measurableSet_Ioi
  have hr' : (0 : ℝ) < r := hr
  simp only [Complex.finrank_real_complex, smul_eq_mul]
  rw [Real.rpow_add_one hr'.ne']
  norm_num
  ring

private lemma nat_int (m : ℕ) :
    Integrable (fun s : ℂ => ‖s‖ ^ m * Real.exp (-Real.pi * ‖s‖ ^ 2)) := by
  have := rad_int (m : ℝ) (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  simpa only [Real.rpow_natCast] using this

private noncomputable def gk (k : ℕ) (s : ℂ) : ℂ :=
  (starRingEnd ℂ s) ^ k * Complex.exp (-(Real.pi : ℂ) * (‖s‖ : ℂ) ^ 2)

private lemma cexp_eq (s : ℂ) : Complex.exp (-(Real.pi : ℂ) * (‖s‖ : ℂ) ^ 2)
    = ((Real.exp (-Real.pi * ‖s‖ ^ 2) : ℝ) : ℂ) := by
  push_cast; rfl

private lemma gk_int (k : ℕ) : Integrable (gk k) := by
  refine Integrable.mono' (nat_int k) ?_ (Filter.Eventually.of_forall fun s => ?_)
  · have := Complex.continuous_conj
    apply Continuous.aestronglyMeasurable
    unfold gk
    fun_prop
  · rw [gk, cexp_eq, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]

private lemma gk_wt (k e : ℕ) (hk : 0 < k) (s : ℂ) :
    gk k s * ((s / (‖s‖ : ℂ)) ^ (k : ℤ) * (‖s‖ : ℂ) ^ (2 * e))
      = ((‖s‖ ^ (k + 2 * e) * Real.exp (-Real.pi * ‖s‖ ^ 2) : ℝ) : ℂ) := by
  by_cases hs : s = 0
  · subst hs
    simp [gk, hk.ne']
  · have h : (‖s‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hs
    have h2 : starRingEnd ℂ s * (s / (‖s‖ : ℂ)) = (‖s‖ : ℂ) := by
      rw [← mul_div_assoc, mul_comm, Complex.mul_conj']
      field_simp
    rw [gk, cexp_eq, zpow_natCast, Complex.ofReal_mul, Complex.ofReal_pow, pow_add]
    have h3 := congrArg (· ^ k) h2
    simp only [mul_pow] at h3
    rw [← h3]
    ring

private lemma rad_pos (m : ℕ) :
    0 < ∫ s : ℂ, ‖s‖ ^ m * Real.exp (-Real.pi * ‖s‖ ^ 2) := by
  refine integral_pos_of_integrable_nonneg_nonzero (x := 1) (by fun_prop) (nat_int m)
    (fun s => by positivity) ?_
  have := Real.exp_pos (-Real.pi)
  simp

private lemma dual_int (k e : ℕ) (hk : 2 * e < k) :
    Integrable (fun y : ℂ => ((-Complex.I * y) ^ k * Complex.exp (-(Real.pi : ℂ) * (‖y‖ : ℂ) ^ 2)) *
      (((y / (‖y‖ : ℂ)) ^ (k : ℤ) * (‖y‖ : ℂ) ^ (2 * e)) * (‖y‖ : ℂ) ^ 2)⁻¹) := by
  have hp : (-2 : ℝ) < (k : ℝ) - ((2 * e + 2 : ℕ) : ℝ) := by
    have : ((2 * e : ℕ) : ℝ) < k := by exact_mod_cast hk
    push_cast at this ⊢
    linarith
  refine Integrable.mono' (rad_int _ hp) ?_ ?_
  · apply Measurable.aestronglyMeasurable
    have h : Measurable fun s : ℂ => (‖s‖ : ℂ) := Complex.measurable_ofReal.comp measurable_norm
    refine Measurable.mul (by fun_prop) (Measurable.inv ?_)
    exact (((measurable_id.div h).pow_const _).mul (h.pow_const _)).mul (h.pow_const _)
  · have h0 : ∀ᵐ y : ℂ, y ≠ 0 := by
      simp [ae_iff]
    filter_upwards [h0] with y hy
    have h : 0 < ‖y‖ := norm_pos_iff.2 hy
    rw [cexp_eq, Real.rpow_sub h, Real.rpow_natCast, Real.rpow_natCast]
    simp only [norm_mul, norm_inv, norm_pow, norm_zpow, norm_div, Complex.norm_real, norm_norm,
      norm_neg, Complex.norm_I, one_mul, div_self h.ne', one_zpow,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    apply le_of_eq
    field_simp
    try ring

theorem UpperTheory.exists_test_fourier_nonvanishing :
    ∀ {ι : Type} [Fintype ι] (κ : ι → ℤ) (e : ℕ), (∀ w, 2 * (e : ℤ) < κ w) → ∃ h : (ι → ℂ) → ℂ, Integrable h ∧
        Integrable (fun s => h s * wt κ e s) ∧ Integrable (fun y => FT h y * dwt κ e y) ∧ ∫ s, h s * wt κ e s ≠ 0 := by
  intro ι _ κ e hκ
  obtain ⟨k, rfl⟩ : ∃ k : ι → ℕ, κ = fun w => (k w : ℤ) :=
    ⟨fun w => (κ w).toNat, funext fun w => by have := hκ w; simp only; omega⟩
  have hk : ∀ w, 2 * e < k w := fun w => by have := hκ w; simp only at this; omega
  have hw : (fun s : ι → ℂ => (∏ w, gk (k w) (s w)) * wt (fun w => (k w : ℤ)) e s)
      = fun s => ∏ w, ((‖s w‖ ^ (k w + 2 * e) * Real.exp (-Real.pi * ‖s w‖ ^ 2) : ℝ) : ℂ) := by
    funext s
    rw [wt, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => gk_wt _ _ (by have := hk w; omega) _
  refine ⟨fun s => ∏ w, gk (k w) (s w), ?_, ?_, ?_, ?_⟩
  · exact Integrable.fintype_prod (f := fun w => gk (k w)) fun w => gk_int _
  · rw [hw]
    exact Integrable.fintype_prod
      (f := fun w (s : ℂ) => ((‖s‖ ^ (k w + 2 * e) * Real.exp (-Real.pi * ‖s‖ ^ 2) : ℝ) : ℂ))
      fun w => (nat_int _).ofReal
  · have hF : (fun y : ι → ℂ => FT (fun s => ∏ w, gk (k w) (s w)) y * dwt (fun w => (k w : ℤ)) e y)
        = fun y => ∏ w, ((-Complex.I * y w) ^ k w * Complex.exp (-(Real.pi : ℂ) * (‖y w‖ : ℂ) ^ 2)) *
      (((y w / (‖y w‖ : ℂ)) ^ (k w : ℤ) * (‖y w‖ : ℂ) ^ (2 * e)) * (‖y w‖ : ℂ) ^ 2)⁻¹ := by
      funext y
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_mul_distrib (g := fun w => (‖y w‖ : ℂ) ^ 2)]
      congr 1
      · simp only [← UpperTheory.gaussian_fourier_conj_power]
        rw [← integral_fintype_prod_volume_eq_prod (fun w (s : ℂ) => (starRingEnd ℂ s) ^ k w *
          Complex.exp (-(Real.pi : ℂ) * (‖s‖ : ℂ) ^ 2) *
          Complex.exp (-(2 * Real.pi * Complex.I) * (((s * y w).re : ℝ) : ℂ))), FT]
        congr 1
        funext s
        rw [Finset.prod_mul_distrib (g := fun w => Complex.exp (-(2 * Real.pi * Complex.I) * (((s w * y w).re : ℝ) : ℂ))),
          ← Complex.exp_sum, ec, Complex.re_sum, Complex.ofReal_sum, Finset.mul_sum]
        rfl
      · simp only [dwt, wt, nm, Complex.ofReal_prod, Complex.ofReal_pow]
    rw [hF]
    exact Integrable.fintype_prod
      (f := fun w (y : ℂ) => ((-Complex.I * y) ^ k w * Complex.exp (-(Real.pi : ℂ) * (‖y‖ : ℂ) ^ 2)) *
      (((y / (‖y‖ : ℂ)) ^ (k w : ℤ) * (‖y‖ : ℂ) ^ (2 * e)) * (‖y‖ : ℂ) ^ 2)⁻¹)
      fun w => dual_int _ _ (hk w)
  · rw [hw, integral_fintype_prod_volume_eq_prod
      (fun w (s : ℂ) => ((‖s‖ ^ (k w + 2 * e) * Real.exp (-Real.pi * ‖s‖ ^ 2) : ℝ) : ℂ))]
    refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    rw [integral_complex_ofReal]
    exact_mod_cast (rad_pos _).ne'
