import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RiemannZetaOneEqOneSubOfRePos

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma exponential_integral_nonneg_real {σ a : ℝ} (hσ : 0 ≤ σ) (ha : 0 < a) :
    ∃ r : ℝ, 0 ≤ r ∧ Formalism.ZF.ComplexPowerDifferenceIntegral.eint (σ : ℂ) a = (r : ℂ) := by
  refine ⟨∫ x in a..(a + 1), (x ^ (-σ) - (a + 1) ^ (-σ)), ?_, ?_⟩
  · apply intervalIntegral.integral_nonneg (by linarith)
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have h1 := Real.rpow_le_rpow_of_nonpos hx0 hx.2 (by linarith : -σ ≤ 0)
    linarith
  · unfold Formalism.ZF.ComplexPowerDifferenceIntegral.eint
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hx0 : 0 ≤ x := le_trans ha.le hx.1
    simp only [Complex.ofReal_sub]
    rw [Complex.ofReal_cpow hx0, Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ a + 1)]
    push_cast
    ring

theorem zeta_negative_real_axis : ZetaNegReal := by
  intro σ hσ0 hσ1
  have hre : 0 < (σ : ℂ).re := by simpa using hσ0
  have hz1 := Formalism.ZF.ComplexPowerDifferenceIntegral.riemannZetaOne_eq_one_sub_of_re_pos hre
  have hne : (σ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne' : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hζ := riemannZeta_eq_inv_sub_mul hne
  choose r hr0 hr using fun n : ℕ =>
    exponential_integral_nonneg_real (σ := σ) (a := (n : ℝ) + 1) hσ0.le (by positivity)
  have hdz : ∀ n : ℕ, Formalism.ZF.ComplexPowerDifferenceIntegral.dz (σ : ℂ) n = ((σ : ℂ) - 1) * ((r n : ℝ) : ℂ) := by
    intro n
    rw [← hr n]
    exact Formalism.ZF.ComplexPowerDifferenceIntegral.d_eq (by positivity) _
  have hsum : Summable r := by
    have hs := Formalism.ZF.ComplexPowerDifferenceIntegral.summable_norm_dz hre
    have hs' : Summable (fun n => ‖((σ : ℂ) - 1)‖⁻¹ * ‖Formalism.ZF.ComplexPowerDifferenceIntegral.dz (σ : ℂ) n‖) := hs.mul_left _
    refine hs'.congr (fun n => ?_)
    rw [hdz n, norm_mul, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne'), one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 n)]
  have hDz : Formalism.ZF.ComplexPowerDifferenceIntegral.Dz (σ : ℂ) = ((σ : ℂ) - 1) * ((∑' n, r n : ℝ) : ℂ) := by
    unfold Formalism.ZF.ComplexPowerDifferenceIntegral.Dz
    simp_rw [hdz]
    rw [tsum_mul_left, Complex.ofReal_tsum]
  set R := ∑' n, r n with hRdef
  have hR0 : 0 ≤ R := tsum_nonneg hr0
  have hval : riemannZeta (σ : ℂ) = ((σ / (σ - 1) - R : ℝ) : ℂ) := by
    rw [hζ, hz1, hDz]
    have hσ1' : (σ - 1 : ℝ) ≠ 0 := by intro h; linarith
    push_cast
    field_simp
  rw [hval, Complex.ofReal_im, Complex.ofReal_re]
  refine ⟨rfl, ?_⟩
  have : σ / (σ - 1) < 0 := div_neg_of_pos_of_neg hσ0 (by linarith)
  linarith

end Formalism.ZeroFreeDirichlet
