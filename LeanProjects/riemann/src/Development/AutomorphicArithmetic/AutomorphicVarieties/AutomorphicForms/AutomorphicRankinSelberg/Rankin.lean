import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory Set CongruenceSubgroup UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Af.Rs
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

private theorem pt_im (x y : ℝ) (hy : 0 < y) : (pt x y).im = y := by
  simp [pt, UpperHalfPlane.ofComplex_apply_of_im_pos, hy]

private theorem coef_zero (k L : ℕ) [NeZero L] (f : CuspForm (Gamma1 L) (k : ℤ)) : coef f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos (by simp)

private theorem integrableOn_rpow_mul_exp_neg_Ioi (A r : ℝ) (hA : 0 < A) (hr : 0 < r) :
    IntegrableOn (fun y : ℝ => y ^ (A - 1) * Real.exp (-r * y)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := A - 1) (b := r)
    (by linarith) one_pos hr
  refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

private theorem integral_rpow_mul_exp_neg_Ioi_eq_gamma_div (A r : ℝ) (hA : 0 < A) (hr : 0 < r) :
    ∫ y in Ioi (0:ℝ), y ^ (A - 1) * Real.exp (-r * y) = Real.Gamma A / r ^ A := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hA hr
  simp only [neg_mul] at h ⊢
  rw [h, Real.div_rpow zero_le_one hr.le, Real.one_rpow]
  ring

private theorem gamma_div_four_pi_mul_rpow_eq (A : ℝ) (n : ℕ) (hn : 0 < n) :
    Real.Gamma A / (4 * Real.pi * n) ^ A = Real.Gamma A / (4 * Real.pi) ^ A / (n : ℝ) ^ A := by
  rw [Real.mul_rpow (by positivity) (by positivity)]
  have h1 : (0:ℝ) < (4 * Real.pi) ^ A := by positivity
  have h2 : (0:ℝ) < (n : ℝ) ^ A := Real.rpow_pos_of_pos (by exact_mod_cast hn) A
  field_simp

theorem UpperTheory.V.Af.Rs.rankin :
    UpperTheory.V.Af.Rs.StripFub → UpperTheory.V.Af.Rs.StripInt → UpperTheory.V.Af.Rs.NicePet → UpperTheory.V.Af.Rs.Pars → UpperTheory.V.Af.Rs.RankSum → UpperTheory.V.Af.Rs.Rankin := by
  intro hFub hInt hNice hPars hSum k L _ f g s hs
  have hs1 : 1 < s := hs.1
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  set A : ℝ := (k:ℝ) + s - 1 with hAdef
  have hA : 0 < A := by rw [hAdef]; linarith
  set a : ℕ → ℂ := fun n => starRingEnd ℂ (coef g n) * coef f n with ha
  have ha0 : a 0 = 0 := by simp [ha, coef_zero k L f]
  set G : ℕ → ℝ → ℂ := fun n y =>
    a n * ((y ^ (A - 1) * Real.exp (-(4 * Real.pi * n) * y) : ℝ) : ℂ) with hG
  have hpt : ∀ y : ℝ, 0 < y →
      (∫ x in (0:ℝ)..1, UpperHalfPlane.petersson (k : ℤ) g f (pt x y) * (((pt x y).im ^ s : ℝ) : ℂ))
        / ((y ^ 2 : ℝ) : ℂ) = ∑' n, G n y := by
    intro y hy
    have h1 : ∀ x : ℝ, UpperHalfPlane.petersson (k : ℤ) g f (pt x y) * (((pt x y).im ^ s : ℝ) : ℂ)
        = (starRingEnd ℂ (g (pt x y)) * f (pt x y)) * ((y : ℂ) ^ k * ((y ^ s : ℝ) : ℂ)) := by
      intro x
      simp only [UpperHalfPlane.petersson, pt_im x y hy, zpow_natCast]
      ring
    have hyA : ((y ^ (A - 1) : ℝ) : ℂ) = (y : ℂ) ^ k * ((y ^ s : ℝ) : ℂ) / ((y ^ 2 : ℝ) : ℂ) := by
      have hr : y ^ (A - 1) = y ^ k * y ^ s / y ^ 2 := by
        rw [show A - 1 = ((k:ℝ) + s) - 2 by rw [hAdef]; ring, Real.rpow_sub hy, Real.rpow_add hy,
          Real.rpow_natCast, Real.rpow_two]
      rw [hr]
      push_cast
      ring
    simp_rw [h1]
    rw [intervalIntegral.integral_mul_const, ← (hPars k L f g y hy).tsum_eq, ← tsum_mul_right,
      ← tsum_div_const]
    congr 1
    ext n
    simp only [hG, ha]
    rw [Complex.ofReal_mul, hyA]
    ring
  have hr : ∀ n : ℕ, 0 < n → (0:ℝ) < 4 * Real.pi * n := fun n hn => by
    have : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  have hGi : ∀ n, Integrable (G n) (volume.restrict (Ioi (0:ℝ))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : G 0 = fun _ => 0 := by funext y; simp [hG, ha0]
      rw [this]
      exact integrable_zero _ _ _
    · exact ((integrableOn_rpow_mul_exp_neg_Ioi A _ hA (hr n hn)).ofReal).const_mul (a n)
  have hsum : Summable (fun n : ℕ => ‖a n‖ / (n:ℝ) ^ A) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (((hSum k L f s hs).add (hSum k L g s hs)).div_const 2)
    have key : ‖coef g n‖ * ‖coef f n‖ ≤ (‖coef f n‖ ^ 2 + ‖coef g n‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖coef f n‖ - ‖coef g n‖)]
    have hn : (0:ℝ) ≤ (n:ℝ) ^ A := by positivity
    calc ‖a n‖ / (n:ℝ) ^ A = (‖coef g n‖ * ‖coef f n‖) / (n:ℝ) ^ A := by
          simp [ha, norm_mul]
      _ ≤ ((‖coef f n‖ ^ 2 + ‖coef g n‖ ^ 2) / 2) / (n:ℝ) ^ A := by gcongr
      _ = _ := by ring
  have hGs : Summable (fun n => ∫ y in Ioi (0:ℝ), ‖G n y‖) := by
    refine (hsum.mul_left (Real.Gamma A / (4 * Real.pi) ^ A)).congr (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hG, ha0]
    · have hc : ∫ y in Ioi (0:ℝ), ‖G n y‖
          = ∫ y in Ioi (0:ℝ), ‖a n‖ * (y ^ (A - 1) * Real.exp (-(4 * Real.pi * n) * y)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
        have hy' : (0:ℝ) < y := hy
        simp only [hG, norm_mul, Complex.norm_real]
        rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le]
      rw [hc, integral_const_mul, integral_rpow_mul_exp_neg_Ioi_eq_gamma_div A _ hA (hr n hn), gamma_div_four_pi_mul_rpow_eq A n hn]
      ring
  have hI := hInt _ (hNice k L f g) s hs
  obtain ⟨-, heq⟩ := hFub _ hI
  show (∫ z in strip, _) = _
  rw [heq, setIntegral_congr_fun measurableSet_Ioi (fun y hy => hpt y hy),
    ← integral_tsum_of_summable_integral_norm hGi hGs, ← tsum_mul_left]
  congr 1
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hG, ha0, coef_zero k L f]
  · simp only [hG]
    rw [integral_const_mul, integral_complex_ofReal, integral_rpow_mul_exp_neg_Ioi_eq_gamma_div A _ hA (hr n hn), gamma_div_four_pi_mul_rpow_eq A n hn, gam]
    have h2 : (0:ℝ) < (n : ℝ) ^ A := Real.rpow_pos_of_pos (by exact_mod_cast hn) A
    push_cast
    field_simp
    simp only [ha]
    ring
