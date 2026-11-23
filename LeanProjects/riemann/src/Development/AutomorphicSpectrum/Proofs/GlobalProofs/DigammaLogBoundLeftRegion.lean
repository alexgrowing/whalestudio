import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaLogBoundRightHalfPlaneStatement

namespace GlobalTheory.CompanionTheory.DigammaLeft

theorem digamma_sub_digamma_one_sub (w : ℂ) (hw : ∀ n : ℤ, w ≠ n) :
    Complex.digamma w - Complex.digamma (1 - w) =
      -((Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)) := by
  have hw1 : ∀ m : ℕ, w ≠ -(m : ℂ) := fun m h => hw (-(m : ℤ)) (by rw [h]; push_cast; rfl)
  have hw2 : ∀ m : ℕ, 1 - w ≠ -(m : ℂ) := fun m h => hw ((m : ℤ) + 1) (by
    push_cast
    linear_combination -h)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : Complex.sin (Real.pi * w) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
    apply hw k
    apply mul_left_cancel₀ hpi
    rw [hk]; ring
  have ha : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hw1
  have hb : Complex.Gamma (1 - w) ≠ 0 := Complex.Gamma_ne_zero hw2
  have hG1 : HasDerivAt Complex.Gamma (deriv Complex.Gamma w) w :=
    (Complex.differentiableAt_Gamma w hw1).hasDerivAt
  have hG2' : HasDerivAt Complex.Gamma (deriv Complex.Gamma (1 - w)) (1 - w) :=
    (Complex.differentiableAt_Gamma (1 - w) hw2).hasDerivAt
  have hlin : HasDerivAt (fun z : ℂ => 1 - z) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have hG2 : HasDerivAt (fun z : ℂ => Complex.Gamma (1 - z))
      (deriv Complex.Gamma (1 - w) * (-1)) w :=
    HasDerivAt.comp w hG2' hlin
  have hprod := hG1.mul hG2
  have hsin : HasDerivAt (fun z : ℂ => Complex.sin (Real.pi * z))
      (Complex.cos (Real.pi * w) * Real.pi) w := by
    have h1 : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z) Real.pi w := by
      simpa using (hasDerivAt_id w).const_mul (Real.pi : ℂ)
    exact (Complex.hasDerivAt_sin _).comp w h1
  have hquot := (hasDerivAt_const w (Real.pi : ℂ)).div hsin hs
  have hfun : ((fun _ : ℂ => (Real.pi : ℂ)) / fun z : ℂ => Complex.sin (Real.pi * z)) =
      (Complex.Gamma * fun z : ℂ => Complex.Gamma (1 - z)) := by
    funext z
    simp only [Pi.mul_apply, Pi.div_apply]
    exact (Complex.Gamma_mul_Gamma_one_sub z).symm
  rw [hfun] at hquot
  have huniq := hprod.unique hquot
  have hab : Complex.Gamma w * Complex.Gamma (1 - w) = Real.pi / Complex.sin (Real.pi * w) :=
    Complex.Gamma_mul_Gamma_one_sub w
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply]
  have e1 : deriv Complex.Gamma w / Complex.Gamma w -
      deriv Complex.Gamma (1 - w) / Complex.Gamma (1 - w) =
      (deriv Complex.Gamma w * Complex.Gamma (1 - w) +
        Complex.Gamma w * (deriv Complex.Gamma (1 - w) * -1)) /
      (Complex.Gamma w * Complex.Gamma (1 - w)) := by
    field_simp
    ring
  rw [e1, huniq, hab]
  field_simp
  ring

theorem sq_norm_sin (z : ℂ) :
    ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.sin_eq, Complex.normSq_apply]
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_mul]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re]
  have h1 := Real.sin_sq_add_cos_sq z.re
  have h2 := Real.cosh_sq z.im
  linear_combination Real.sin z.re ^ 2 * h2 + Real.sinh z.im ^ 2 * h1

theorem sq_norm_cos (z : ℂ) :
    ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.cos_eq, Complex.normSq_apply]
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_mul]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re]
  have h1 := Real.sin_sq_add_cos_sq z.re
  have h2 := Real.cosh_sq z.im
  linear_combination Real.cos z.re ^ 2 * h2 + Real.sinh z.im ^ 2 * h1

theorem norm_cos_le_of_im (z : ℂ) (h : 1 ≤ |z.im|) : ‖Complex.cos z‖ ≤ 2 * ‖Complex.sin z‖ := by
  have h1 : 1 ≤ |Real.sinh z.im| := by
    rw [Real.abs_sinh]
    exact h.trans (Real.self_le_sinh_iff.mpr (abs_nonneg _))
  have h2 : 1 ≤ Real.sinh z.im ^ 2 := by
    rw [← sq_abs]; nlinarith
  have hc := sq_norm_cos z
  have hs := sq_norm_sin z
  apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
  rw [mul_pow, hc, hs]
  nlinarith [Real.cos_sq_le_one z.re, sq_nonneg (Real.sin z.re)]

theorem norm_cos_le_of_re (z : ℂ) (k : ℤ) (h : z.re = Real.pi * ((k : ℝ) / 2 + 1 / 4)) :
    ‖Complex.cos z‖ ≤ 2 * ‖Complex.sin z‖ := by
  have hc := sq_norm_cos z
  have hs := sq_norm_sin z
  have h2 : Real.cos (2 * z.re) = 0 := by
    have : 2 * z.re = (k : ℝ) * Real.pi + Real.pi / 2 := by rw [h]; ring
    rw [this, Real.cos_add_pi_div_two, Real.sin_int_mul_pi, neg_zero]
  have h3 : Real.cos z.re ^ 2 = Real.sin z.re ^ 2 := by
    have := Real.cos_sq' z.re
    rw [Real.cos_two_mul] at h2
    nlinarith
  apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
  rw [mul_pow, hc, hs, h3]
  nlinarith [sq_nonneg (Real.sin z.re), sq_nonneg (Real.sinh z.im)]

theorem norm_digamma_le_left :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w.re ≤ 1 / 4 →
      (1 / 2 ≤ |w.im| ∨ ∃ k : ℤ, w.re = (k : ℝ) / 2 + 1 / 4) →
      ‖Complex.digamma w‖ ≤ C * Real.log (‖w‖ + 2) := by
  obtain ⟨C, hC, hb⟩ := GlobalTheory.T.digamma_log_bound_right_half_plane
  refine ⟨2 * C + 10, by positivity, fun w hre halt => ?_⟩
  have hint : ∀ n : ℤ, w ≠ n := by
    intro n hn
    rcases halt with h | ⟨k, hk⟩
    · rw [hn] at h
      norm_num at h
    · have h1 : (n : ℝ) = (k : ℝ) / 2 + 1 / 4 := by
        rw [← hk, hn]; simp
      have h4 : (4 * n : ℝ) = 2 * k + 1 := by linarith
      have h5 : 4 * n = 2 * k + 1 := by exact_mod_cast h4
      omega
  have hcot : ‖Complex.cos (Real.pi * w)‖ ≤ 2 * ‖Complex.sin (Real.pi * w)‖ := by
    rcases halt with h | ⟨k, hk⟩
    · apply norm_cos_le_of_im
      have him : ((Real.pi : ℂ) * w).im = Real.pi * w.im := by simp
      rw [him, abs_mul, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    · apply norm_cos_le_of_re _ k
      simp [hk]
  have hcotn : ‖(Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)‖ ≤
      2 * Real.pi := by
    rcases eq_or_ne (Complex.sin (Real.pi * w)) 0 with h0 | h0
    · rw [h0]
      simp [Real.pi_pos.le]
    · have hpos : 0 < ‖Complex.sin (Real.pi * w)‖ := norm_pos_iff.mpr h0
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        div_le_iff₀ hpos]
      nlinarith [Real.pi_pos]
  have hrefl := digamma_sub_digamma_one_sub w hint
  have hdecomp : Complex.digamma w = Complex.digamma (1 - w) +
      -((Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)) := by
    rw [← hrefl]; ring
  have hbd := hb (1 - w) (by simp; linarith)
  have hw0 := norm_nonneg w
  have hL : Real.log 2 ≤ Real.log (‖w‖ + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h1w : ‖1 - w‖ ≤ 1 + ‖w‖ := by simpa using norm_sub_le 1 w
  have hl2 : Real.log (‖1 - w‖ + 2) ≤ 2 * Real.log (‖w‖ + 2) := by
    have h2 : Real.log (‖1 - w‖ + 2) ≤ Real.log ((‖w‖ + 2) ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rwa [Real.log_pow, Nat.cast_ofNat] at h2
  have hpi : 2 * Real.pi ≤ 10 * Real.log (‖w‖ + 2) := by
    linarith [Real.pi_lt_d2, Real.log_two_gt_d9]
  have hmul : C * Real.log (‖1 - w‖ + 2) ≤ C * (2 * Real.log (‖w‖ + 2)) :=
    mul_le_mul_of_nonneg_left hl2 hC.le
  calc ‖Complex.digamma w‖
      ≤ ‖Complex.digamma (1 - w)‖ +
          ‖(Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)‖ := by
        rw [hdecomp]
        simpa using norm_add_le (Complex.digamma (1 - w))
          (-((Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)))
    _ ≤ (2 * C + 10) * Real.log (‖w‖ + 2) := by nlinarith

end GlobalTheory.CompanionTheory.DigammaLeft
