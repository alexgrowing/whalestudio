import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveDens

theorem angleForm_alg (n : ℕ) (q P D H β β' L L' : ℂ) (a a' : ℝ) (ha : 0 < a) (ha' : 0 < a')
    (Qi dQi dv R dR : ℂ)
    (hQi : Qi = (((a * a')⁻¹ : ℝ) : ℂ))
    (hdQi : dQi = (((-((a * a') ^ 2)⁻¹ : ℝ) : ℂ)) *
      ((a : ℂ) * ((a' : ℂ) * starRingEnd ℂ β') + (a : ℂ) * starRingEnd ℂ β * (a' : ℂ)))
    (hdv : dv = q * starRingEnd ℂ q * dQi + (q * starRingEnd ℂ P + D * starRingEnd ℂ q) * Qi)
    (hR : R = starRingEnd ℂ q * (P - q * β') - q * (starRingEnd ℂ D - starRingEnd ℂ q * β))
    (hdR : dR = (starRingEnd ℂ q * (H - (q * L' + D * β')) + starRingEnd ℂ P * (P - q * β')) -
          (q * (starRingEnd ℂ H - (starRingEnd ℂ q * L + starRingEnd ℂ P * β)) +
            D * (starRingEnd ℂ D - starRingEnd ℂ q * β))) :
    ((((‖q‖ ^ 2 / (a * a')) ^ n : ℝ) : ℂ) * (R * dQi + dR * Qi) +
      (((n : ℝ) * (‖q‖ ^ 2 / (a * a')) ^ (n - 1) : ℝ) : ℂ) * dv * (R * Qi)).re =
    (n + 1) * (‖q‖ ^ 2 / (a * a')) ^ n * ((‖P - q * β'‖ ^ 2 - ‖D - q * starRingEnd ℂ β‖ ^ 2) / (a * a')) +
      (‖q‖ ^ 2 / (a * a')) ^ (n + 1) * (L.re - L'.re) := by
  subst hQi hdQi hdv hR hdR
  have hQ : (0:ℝ) < a * a' := mul_pos ha ha'
  have ha0 : a ≠ 0 := ha.ne'
  have ha0' : a' ≠ 0 := ha'.ne'
  obtain ⟨K, m, hK, hn⟩ : ∃ K m, K = (‖q‖ ^ 2 / (a * a')) ^ m ∧
      ((‖q‖ ^ 2 / (a * a')) ^ n = K * (‖q‖ ^ 2 / (a * a')) ∧
        ((n : ℝ) * (‖q‖ ^ 2 / (a * a')) ^ (n - 1)) = n * K ∧ (n:ℝ) ≠ 0 ∨
       (‖q‖ ^ 2 / (a * a')) ^ n = 1 ∧ ((n : ℝ) * (‖q‖ ^ 2 / (a * a')) ^ (n - 1)) = 0 ∧ n = 0) := by
    rcases n with _ | m
    · exact ⟨1, 0, by simp, Or.inr ⟨by simp, by simp, rfl⟩⟩
    · refine ⟨_, m, rfl, Or.inl ⟨pow_succ _ _, by simp, by positivity⟩⟩
  have hpow : (‖q‖ ^ 2 / (a * a')) ^ (n + 1) = (‖q‖ ^ 2 / (a * a')) ^ n * (‖q‖ ^ 2 / (a * a')) := pow_succ _ _
  rw [hpow]
  rcases hn with ⟨h1, h2, -⟩ | ⟨h1, h2, rfl⟩
  · rw [h1, h2]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
    field_simp
    ring
  · rw [h1]
    simp only [Nat.cast_zero, zero_mul, Complex.ofReal_zero, add_zero, zero_add, one_mul,
      Complex.ofReal_one]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
    field_simp
    ring

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem differentiableAt_del_apply_of_contDiffAt_two {f : E → ℂ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (w : E) : DifferentiableAt ℝ (fun x => del f x w) z := by
  have h := differentiableAt_fderiv_of_contDiffAt_two hf
  simp only [del_apply]
  exact ((h.clm_apply (differentiableAt_const _)).sub
    ((h.clm_apply (differentiableAt_const _)).const_smul Complex.I)).const_smul (1 / 2 : ℂ)

theorem re_dbar_angleForm (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E)
    (ha : ContDiffAt ℝ 2 a z) (ha' : ContDiffAt ℝ 2 a' z) (hq : ContDiffAt ℝ 2 q z)
    (h0 : 0 < a z) (h0' : 0 < a' z) :
    (dbar (angleForm n a a' q ξ) z ξ).re = (n + 1) * (‖q z‖ ^ 2 / (a z * a' z)) ^ n *
      ((‖del q z ξ - q z * del (fun x => (Real.log (a' x) : ℂ)) z ξ‖ ^ 2 -
        ‖dbar q z ξ - q z * dbar (fun x => (Real.log (a x) : ℂ)) z ξ‖ ^ 2) / (a z * a' z)) +
      (‖q z‖ ^ 2 / (a z * a' z)) ^ (n + 1) *
        ((leviForm (fun x => Real.log (a x)) z ξ ξ).re -
          (leviForm (fun x => Real.log (a' x)) z ξ ξ).re) := by
  have hq1 : DifferentiableAt ℝ q z := hq.differentiableAt (by norm_num)
  have ha1 : DifferentiableAt ℝ a z := ha.differentiableAt (by norm_num)
  have ha1' : DifferentiableAt ℝ a' z := ha'.differentiableAt (by norm_num)
  have hαC : ContDiffAt ℝ 2 (fun x => (Real.log (a x) : ℂ)) z :=
    contDiffAt_ofReal_comp (ha.log h0.ne')
  have hαC' : ContDiffAt ℝ 2 (fun x => (Real.log (a' x) : ℂ)) z :=
    contDiffAt_ofReal_comp (ha'.log h0'.ne')
  have hqc : ContDiffAt ℝ 2 (fun x => starRingEnd ℂ (q x)) z :=
    (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.contDiffAt.comp z hq
  have dP := differentiableAt_del_apply_of_contDiffAt_two hq ξ
  have dPt := differentiableAt_del_apply_of_contDiffAt_two hqc ξ
  have dB := differentiableAt_del_apply_of_contDiffAt_two hαC ξ
  have dB' := differentiableAt_del_apply_of_contDiffAt_two hαC' ξ
  have dqc : DifferentiableAt ℝ (fun x => starRingEnd ℂ (q x)) z := hqc.differentiableAt (by norm_num)
  have daC : DifferentiableAt ℝ (fun x => (a x : ℂ)) z :=
    (contDiffAt_ofReal_comp ha).differentiableAt (by norm_num)
  have daC' : DifferentiableAt ℝ (fun x => (a' x : ℂ)) z :=
    (contDiffAt_ofReal_comp ha').differentiableAt (by norm_num)
  have hQ1 : DifferentiableAt ℝ (fun x => a x * a' x) z := ha1.mul ha1'
  have hQ0 : a z * a' z ≠ 0 := (mul_pos h0 h0').ne'
  have hv1 : DifferentiableAt ℝ (fun x => ‖q x‖ ^ 2 / (a x * a' x)) z :=
    ((hq1.norm_sq (𝕜 := ℂ)).mul (hQ1.inv hQ0)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by simp only [div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply])
  have dQi : DifferentiableAt ℝ (fun x => (((a x * a' x)⁻¹ : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z (hQ1.inv hQ0)
  have dW : DifferentiableAt ℝ (fun x => (((‖q x‖ ^ 2 / (a x * a' x)) ^ n : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z (hv1.pow n)
  have dR : DifferentiableAt ℝ (fun x => starRingEnd ℂ (q x) *
      (del q x ξ - q x * del (fun y => (Real.log (a' y) : ℂ)) x ξ) -
      q x * (del (fun y => starRingEnd ℂ (q y)) x ξ -
        starRingEnd ℂ (q x) * del (fun y => (Real.log (a y) : ℂ)) x ξ)) z :=
    (dqc.mul (dP.sub (hq1.mul dB'))).sub (hq1.mul (dPt.sub (dqc.mul dB)))
  have hG : angleForm n a a' q ξ = fun x =>
      (((‖q x‖ ^ 2 / (a x * a' x)) ^ n : ℝ) : ℂ) *
        ((starRingEnd ℂ (q x) * (del q x ξ - q x * del (fun y => (Real.log (a' y) : ℂ)) x ξ) -
            q x * (del (fun y => starRingEnd ℂ (q y)) x ξ -
              starRingEnd ℂ (q x) * del (fun y => (Real.log (a y) : ℂ)) x ξ)) *
          (((a x * a' x)⁻¹ : ℝ) : ℂ)) := by
    funext x
    rw [angleForm, map_sub, map_mul, dbar_ofReal (fun y => Real.log (a y)), Complex.conj_conj,
      ← del_conj]
    push_cast
    ring
  rw [dbar_ofReal (fun x => Real.log (a x)) z ξ, hG, dbar_mul dW (dR.fun_mul dQi) ξ, dbar_mul dR dQi ξ]
  beta_reduce
  have hW := dbar_ofReal_comp (h := fun s : ℝ => s ^ n) (hasDerivAt_pow n _) hv1 ξ
  beta_reduce at hW
  rw [hW, del_conj q z ξ]
  refine angleForm_alg n (q z) (del q z ξ) (dbar q z ξ) (ddbar q z ξ ξ)
    (del (fun x => (Real.log (a x) : ℂ)) z ξ) (del (fun x => (Real.log (a' x) : ℂ)) z ξ)
    (leviForm (fun x => Real.log (a x)) z ξ ξ) (leviForm (fun x => Real.log (a' x)) z ξ ξ)
    (a z) (a' z) h0 h0' _ _ _ _ _ rfl ?_ ?_ rfl ?_
  · have h1 := dbar_ofReal_comp (t := fun x => a x * a' x) (h := fun s : ℝ => s⁻¹)
      (hasDerivAt_inv (x := a z * a' z) hQ0) hQ1 ξ
    beta_reduce at h1
    have h2 : (fun x => ((a x * a' x : ℝ) : ℂ)) = fun x => (a x : ℂ) * (a' x : ℂ) := by
      funext x; push_cast; rfl
    have hda := dbar_ofReal_comp (h := Real.log) (Real.hasDerivAt_log h0.ne') ha1 ξ
    have hda' := dbar_ofReal_comp (h := Real.log) (Real.hasDerivAt_log h0'.ne') ha1' ξ
    rw [dbar_ofReal] at hda hda'
    have hz : (a z : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    have hz' : (a' z : ℂ) ≠ 0 := by exact_mod_cast h0'.ne'
    have e1 : dbar (fun x => (a x : ℂ)) z ξ =
        (a z : ℂ) * starRingEnd ℂ (del (fun x => (Real.log (a x) : ℂ)) z ξ) := by
      rw [hda]; push_cast; field_simp
    have e2 : dbar (fun x => (a' x : ℂ)) z ξ =
        (a' z : ℂ) * starRingEnd ℂ (del (fun x => (Real.log (a' x) : ℂ)) z ξ) := by
      rw [hda']; push_cast; field_simp
    rw [h1, h2, dbar_mul daC daC' ξ, e1, e2]
  · have h3 : (fun x => ((‖q x‖ ^ 2 / (a x * a' x) : ℝ) : ℂ)) =
        fun x => q x * starRingEnd ℂ (q x) * (((a x * a' x)⁻¹ : ℝ) : ℂ) := by
      funext x; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [h3, dbar_mul (hq1.fun_mul dqc) dQi ξ, dbar_mul hq1 dqc ξ, dbar_conj]
  · rw [dbar_sub (dqc.fun_mul (dP.fun_sub (hq1.fun_mul dB')))
        (hq1.fun_mul (dPt.fun_sub (dqc.fun_mul dB))),
      ContinuousLinearMap.sub_apply, dbar_mul dqc (dP.fun_sub (hq1.fun_mul dB')) ξ,
      dbar_mul hq1 (dPt.fun_sub (dqc.fun_mul dB)) ξ,
      dbar_sub dP (hq1.fun_mul dB'), dbar_sub dPt (dqc.fun_mul dB),
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      dbar_mul hq1 dB' ξ, dbar_mul dqc dB ξ, dbar_conj,
      ← ddbar_eq_dbar_del hq, ← ddbar_eq_dbar_del hqc, ← ddbar_eq_dbar_del hαC,
      ← ddbar_eq_dbar_del hαC', ddbar_conj hq, del_conj q z ξ]
    rfl

end GlobalTheory.CurveDens
