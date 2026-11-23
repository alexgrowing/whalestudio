import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.OneMom

noncomputable section

open MeasureTheory Set Real

namespace PositivityTheory.Rg.Sw.LC.Mom1

theorem norm_integrand (c : ℝ) (p q : ℕ) (z : ℂ) :
    ‖z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))‖ =
      ‖z‖ ^ ((p + q : ℕ) : ℝ) * Real.exp (-c * ‖z‖ ^ (2 : ℝ)) := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_star, Complex.norm_exp_ofReal, Real.rpow_natCast,
    Real.rpow_two, pow_add]
  ring_nf

theorem integrable_rpow_gauss (c : ℝ) (hc : 0 < c) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun z : ℂ => ‖z‖ ^ s * Real.exp (-c * ‖z‖ ^ (2 : ℝ))) := by
  by_contra h
  have h1 := Complex.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := s) (b := c) (by norm_num)
    (by linarith) hc
  rw [integral_undef h] at h1
  have hG := Real.Gamma_pos_of_pos (s := (s + 2) / 2) (by linarith)
  have : 0 < (2 * π / 2) * c ^ (-(s + 2) / 2) * Real.Gamma ((s + 2) / 2) := by
    have := Real.pi_pos
    positivity
  linarith

theorem continuous_integrand (c : ℝ) (p q : ℕ) :
    Continuous (fun z : ℂ => z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))) :=
  ((continuous_pow p).mul (continuous_star.pow q)).mul
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
      ((continuous_const.mul (continuous_norm.pow 2)).neg)))

theorem integrable_integrand (c : ℝ) (hc : 0 < c) (p q : ℕ) :
    Integrable (fun z : ℂ => z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))) :=
  (integrable_rpow_gauss c hc ((p + q : ℕ) : ℝ) (by positivity)).mono'
    (continuous_integrand c p q).aestronglyMeasurable
    (ae_of_all _ fun z => (norm_integrand c p q z).le)

theorem integral_diag (c : ℝ) (hc : 0 < c) (p : ℕ) :
    ∫ z : ℂ, z ^ p * star z ^ p * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) =
      ((Real.pi * (p.factorial : ℝ) / c ^ (p + 1) : ℝ) : ℂ) := by
  have e : ∀ z : ℂ, z ^ p * star z ^ p * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) =
      ((‖z‖ ^ ((2 * p : ℕ) : ℝ) * Real.exp (-c * ‖z‖ ^ (2 : ℝ)) : ℝ) : ℂ) := by
    intro z
    rw [← mul_pow, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Real.rpow_natCast,
      Real.rpow_two]
    push_cast
    rw [pow_mul]
    ring_nf
  simp_rw [e]
  rw [integral_complex_ofReal, Complex.integral_rpow_mul_exp_neg_mul_rpow (by norm_num)
    (by have : (0 : ℝ) ≤ ((2 * p : ℕ) : ℝ) := by positivity
        linarith) hc]
  congr 1
  have h1 : ((((2 * p : ℕ) : ℝ) + 2) / 2) = (p : ℝ) + 1 := by push_cast; ring
  rw [h1, show (-(((2 * p : ℕ) : ℝ) + 2) / 2) = -((p : ℝ) + 1) by push_cast; ring,
    Real.Gamma_nat_eq_factorial, Real.rpow_neg hc.le, show ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]
  field_simp

theorem integral_offdiag (c : ℝ) (p q : ℕ) (hpq : p ≠ q) :
    ∫ z : ℂ, z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) = 0 := by
  set F : ℂ → ℂ := fun z => z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) with hF
  set f : ℝ → ℂ := fun r => (r : ℂ) ^ (p + q + 1) * Complex.exp ((-(c * r ^ 2) : ℝ)) with hf
  set k : ℂ := ((p : ℂ) - q) * Complex.I with hk
  set g : ℝ → ℂ := fun θ => Complex.exp (k * θ) with hg
  have hk0 : k ≠ 0 := by
    rw [hk]
    refine mul_ne_zero ?_ Complex.I_ne_zero
    rw [sub_ne_zero]
    exact_mod_cast hpq
  have hpt : ∀ x ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π, x.1 • F (Complex.polarCoord.symm x) = f x.1 * g x.2 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    simp only [mem_Ioi] at hr
    have he : ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I = Complex.exp (θ * Complex.I) := by
      rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    have hn : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    simp only [hF, hf, hg, hk]
    rw [hn, Complex.polarCoord_symm_apply]
    simp only
    rw [he, Complex.real_smul, star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj,
      mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    have hc : (starRingEnd ℂ) ((θ : ℂ) * Complex.I) = -((θ : ℂ) * Complex.I) := by
      simp [Complex.conj_ofReal]
    rw [hc]
    have : Complex.exp (↑p * (↑θ * Complex.I)) * Complex.exp (↑q * -(↑θ * Complex.I)) =
        Complex.exp (((p : ℂ) - q) * Complex.I * θ) := by
      rw [← Complex.exp_add]; congr 1; ring
    calc (r : ℂ) * ((r : ℂ) ^ p * Complex.exp (↑p * (↑θ * Complex.I)) *
            ((r : ℂ) ^ q * Complex.exp (↑q * -(↑θ * Complex.I))) * Complex.exp ((-(c * r ^ 2) : ℝ)))
        = (r : ℂ) ^ (p + q + 1) * Complex.exp ((-(c * r ^ 2) : ℝ)) *
            (Complex.exp (↑p * (↑θ * Complex.I)) * Complex.exp (↑q * -(↑θ * Complex.I))) := by ring
      _ = _ := by rw [this]
  have hgI : ∫ θ in Ioo (-π) π, g θ = 0 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      hg]
    simp only
    rw [integral_exp_mul_complex hk0]
    have : k * (π : ℂ) = k * ((-π : ℝ) : ℂ) + (((p : ℤ) - q : ℤ) : ℂ) * (2 * π * Complex.I) := by
      rw [hk]; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, sub_self, zero_div]
  rw [← Complex.integral_comp_polarCoord_symm F, polarCoord_target,
    setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hpt, Measure.volume_eq_prod,
    setIntegral_prod_mul f g, hgI, mul_zero]

theorem oneMom : OneMom := by
  intro c hc p q
  refine ⟨integrable_integrand c hc p q, ?_⟩
  split_ifs with h
  · subst h; exact integral_diag c hc p
  · exact integral_offdiag c p q h

end PositivityTheory.Rg.Sw.LC.Mom1

namespace PositivityTheory.Rg.Sw.LC

theorem oneMom : OneMom := Mom1.oneMom

end PositivityTheory.Rg.Sw.LC
