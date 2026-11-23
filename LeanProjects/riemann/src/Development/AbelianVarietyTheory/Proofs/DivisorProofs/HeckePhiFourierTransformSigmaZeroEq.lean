import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierLipschitzOneVariableKernelEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIsBigORpowLipschitzProductKernel

noncomputable section

open Complex MeasureTheory Set
open scoped FourierTransform

namespace GlobalTheory.HeckeTwo

lemma lipschitzOneVariableKernel_two_eq_indicator {y : ℝ} (hy : 0 < y) :
    GlobalTheory.LipschitzTR.phi1 2 ((y : ℂ) * I) =
      (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ 1 * Complex.exp (-(((2 * Real.pi * y : ℝ) : ℂ) * t))) := by
  funext t
  have him : ((y : ℂ) * I).im = y := by simp
  simp only [GlobalTheory.LipschitzTR.phi1, Set.indicator, Set.mem_Ioi, him, sign_pos hy, SignType.coe_one, one_mul]
  by_cases ht : 0 < t
  · rw [if_pos ht, if_pos ht, abs_of_pos ht]
    push_cast
    congr 2
    ring_nf
    rw [I_sq]
    ring
  · rw [if_neg ht, if_neg ht]

lemma norm_inv_ofReal_add_mul_I_sq (x y : ℝ) : ‖((x : ℂ) + (y : ℂ) * I)⁻¹ ^ 2‖ = (x ^ 2 + y ^ 2)⁻¹ := by
  rw [norm_pow, norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

lemma ofReal_add_ofReal_mul_I_ne_zero (x : ℝ) {y : ℝ} (hy : 0 < y) : (x : ℂ) + (y : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy.ne' this

theorem hTrans_sigma_zero_eq : ∀ (ν y : ℝ), 0 < y → GlobalTheory.HeckeTwo.hTrans 0 ν y =
    if 0 < ν then -4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((Real.exp (-(2 * Real.pi * ν * y)) : ℝ) : ℂ) else 0 := by
  intro ν y hy
  set g := GlobalTheory.LipschitzTR.phi1 2 ((y : ℂ) * I) with hg
  have hw : ((y : ℂ) * I).im ≠ 0 := by simp [hy.ne']
  have hgc : Continuous g := GlobalTheory.LipschitzTR.continuous_lipschitzOneVariableKernel le_rfl hw
  have hgi : Integrable g := by
    rw [hg, lipschitzOneVariableKernel_two_eq_indicator hy, integrable_indicator_iff measurableSet_Ioi]
    exact GlobalTheory.LipschitzTR.integrableOn_pow_mul_cexp_neg 1 (by simp; positivity)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hF : ∀ x : ℝ, 𝓕 g x = -(4 * (Real.pi : ℂ) ^ 2)⁻¹ * (((-x : ℝ) : ℂ) + (y : ℂ) * I)⁻¹ ^ 2 := by
    intro x
    rw [hg, GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow 2 le_rfl even_two _ hw x]
    have hne := ofReal_add_ofReal_mul_I_ne_zero (-x) hy
    rw [zpow_neg, zpow_natCast]
    push_cast at hne ⊢
    have : (y : ℂ) * I - x = -(x : ℂ) + y * I := by ring
    rw [this]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hFi : Integrable (𝓕 g) := by
    have hb : Integrable (fun x : ℝ => ((4 * Real.pi ^ 2 * y ^ 2)⁻¹ : ℝ) * (1 + (x / y) ^ 2)⁻¹) :=
      (integrable_inv_one_add_sq.comp_div hy.ne').const_mul _
    refine hb.mono' ?_ (Filter.Eventually.of_forall fun x => le_of_eq ?_)
    · rw [show (𝓕 g) = fun x : ℝ => -(4 * (Real.pi : ℂ) ^ 2)⁻¹ * (((-x : ℝ) : ℂ) + (y : ℂ) * I)⁻¹ ^ 2 from funext hF]
      exact Continuous.aestronglyMeasurable
        (continuous_const.mul ((((continuous_ofReal.comp continuous_neg).add continuous_const).inv₀
          (fun x => ofReal_add_ofReal_mul_I_ne_zero (-x) hy)).pow 2))
    · rw [hF, norm_mul, norm_neg, norm_inv, norm_mul, norm_pow, norm_inv_ofReal_add_mul_I_sq]
      simp only [RCLike.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, neg_sq]
      have : y ≠ 0 := hy.ne'
      field_simp <;> ring
  have hinv : 𝓕 (𝓕⁻ g) = g := hgc.fourier_fourierInv_eq hgi hFi
  have hphi : ∀ t : ℝ, phi 0 ((t : ℂ) + (y : ℂ) * I) = -4 * (Real.pi : ℂ) ^ 2 * 𝓕⁻ g t := by
    intro t
    rw [Real.fourierInv_eq_fourier_neg, hF, neg_neg]
    unfold phi
    rw [mul_zero, Complex.cpow_zero, mul_one]
    field_simp
  have hT : hTrans 0 ν y = -4 * (Real.pi : ℂ) ^ 2 * 𝓕 (𝓕⁻ g) ν := by
    unfold hTrans
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    congr 1
    funext t
    rw [hphi t, smul_eq_mul]
    push_cast
    ring_nf
  rw [hT, hinv, hg]
  simp only [GlobalTheory.LipschitzTR.phi1]
  have him : ((y : ℂ) * I).im = y := by simp
  rw [him, sign_pos hy, SignType.coe_one, one_mul]
  by_cases hν : 0 < ν
  · rw [if_pos hν, if_pos hν, abs_of_pos hν]
    push_cast
    ring_nf
    rw [I_sq]
    ring_nf
  · rw [if_neg hν, if_neg hν, mul_zero]

end GlobalTheory.HeckeTwo
