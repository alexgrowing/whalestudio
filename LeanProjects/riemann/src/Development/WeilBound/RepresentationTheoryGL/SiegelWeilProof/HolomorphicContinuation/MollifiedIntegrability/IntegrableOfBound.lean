import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.WR.Ib

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

variable {n : ℕ}

def lf (t : ℝ) (β : E n) : E n →L[ℝ] ℂ :=
  ∑ a, ∑ b, (-(Complex.I * t * β a b)) • (Complex.ofRealCLM.comp
    ((ContinuousLinearMap.proj b : (Fin n → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj a : E n →L[ℝ] (Fin n → ℝ))))

theorem lf_apply (t : ℝ) (β w : E n) :
    lf t β w = -(Complex.I * t * ∑ a, ∑ b, (β a b : ℂ) * (w a b : ℂ)) := by
  simp only [lf, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem chr_eq (t : ℝ) (β y : E n) : chr t β y = Complex.exp (lf t β y) := by
  rw [lf_apply, chr]
  push_cast
  rfl

theorem hasFDerivAt_chr (t : ℝ) (β y : E n) : HasFDerivAt (chr t β) (chr t β y • lf t β) y := by
  have e : chr t β = fun y => Complex.exp (lf t β y) := funext (chr_eq t β)
  rw [e]
  exact (lf t β).hasFDerivAt.cexp

theorem fderiv_chr (t : ℝ) (β y w : E n) : fderiv ℝ (chr t β) y w = chr t β y * lf t β w := by
  rw [(hasFDerivAt_chr t β y).fderiv]
  simp [smul_eq_mul]

theorem differentiable_chr (t : ℝ) (β : E n) : Differentiable ℝ (chr t β) :=
  fun y => (hasFDerivAt_chr t β y).differentiableAt

theorem continuous_chr (t : ℝ) (β : E n) : Continuous (chr t β) := (differentiable_chr t β).continuous

theorem norm_chr (t : ℝ) (β y : E n) : ‖chr t β y‖ = 1 := by
  rw [chr_eq, Complex.norm_exp, lf_apply]
  have h : (∑ a, ∑ b, (β a b : ℂ) * (y a b : ℂ)) = ((∑ a, ∑ b, β a b * y a b : ℝ) : ℂ) := by push_cast; rfl
  rw [h]
  simp [Complex.mul_re, Complex.I_re, Complex.I_im]

theorem lf_re_im (t : ℝ) (β : E n) (w : Fin n → Fin n → ℂ) :
    lf t β (fun a b => (w a b).re) + Complex.I * lf t β (fun a b => (w a b).im) =
      -(Complex.I * t * ∑ a, ∑ b, (β a b : ℂ) * w a b) := by
  rw [lf_apply, lf_apply]
  have h : ∀ a b, (β a b : ℂ) * w a b =
      (β a b : ℂ) * ((w a b).re : ℂ) + Complex.I * ((β a b : ℂ) * ((w a b).im : ℂ)) := by
    intro a b
    conv_lhs => rw [← Complex.re_add_im (w a b)]
    ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem herm_apply' (x : E n) (i j : Fin n) :
    herm x i j = ((x i j + x j i : ℝ) : ℂ) / 2 + Complex.I * ((x i j - x j i : ℝ) : ℂ) / 2 := rfl

theorem sum_single (β : E n) (c : ℂ) (k l : Fin n) :
    ∑ a, ∑ b, (β a b : ℂ) * (if a = k ∧ b = l then c else 0) = β k l * c := by
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single l]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    simp [ha]
  · simp

theorem sum_vkl (β : E n) (k l : Fin n) : ∑ a, ∑ b, (β a b : ℂ) * vkl k l a b = herm β k l := by
  simp only [vkl, mul_add, Finset.sum_add_distrib, sum_single]
  rw [herm_apply']
  push_cast
  ring

theorem dkl_chr (t : ℝ) (β : E n) (k l : Fin n) (y : E n) :
    Dkl k l (chr t β) y = (-(Complex.I * t) * herm β k l) * chr t β y := by
  have h := lf_re_im t β (vkl k l)
  rw [sum_vkl] at h
  simp only [Dkl, dirC, fderiv_chr]
  linear_combination (chr t β y) * h

theorem conj_half_add : starRingEnd ℂ ((1 + Complex.I) / 2) = (1 - Complex.I) / 2 := by
  rw [map_div₀, map_add, map_one, Complex.conj_I, map_ofNat]; ring

theorem conj_half_sub : starRingEnd ℂ ((1 - Complex.I) / 2) = (1 + Complex.I) / 2 := by
  rw [map_div₀, map_sub, map_one, Complex.conj_I, map_ofNat]; ring

theorem vkl_swap (k l a b : Fin n) : vkl l k a b = starRingEnd ℂ (vkl k l a b) := by
  simp only [vkl, map_add, apply_ite (starRingEnd ℂ), map_zero, conj_half_add, conj_half_sub]
  rw [add_comm]

theorem dkl_swap (g : E n → ℂ) (k l : Fin n) (y : E n) :
    Dkl l k g y = fderiv ℝ g y (fun a b => (vkl k l a b).re) -
      Complex.I * fderiv ℝ g y (fun a b => (vkl k l a b).im) := by
  have e1 : (fun a b => (vkl l k a b).re) = fun a b => (vkl k l a b).re := by
    funext a b; rw [vkl_swap]; simp
  have e2 : (fun a b => (vkl l k a b).im) = -(fun a b => (vkl k l a b).im) := by
    funext a b; rw [vkl_swap]; simp
  simp only [Dkl, dirC]
  rw [e1, e2, map_neg]
  ring

theorem contDiff_dkl {g : E n → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (k l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Dkl k l g) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ g) := (contDiff_infty_iff_fderiv.mp hg).2
  simp only [Dkl, dirC]
  exact (hd.clm_apply contDiff_const).add (contDiff_const.mul (hd.clm_apply contDiff_const))

theorem integrable_of_bound {g : E n → ℂ} (hg : Continuous g) {h : E n → ℝ} (hh : Integrable h)
    (hb : ∀ y, ‖g y‖ ≤ h y) : Integrable g :=
  hh.mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)

theorem integrable_mul_chr {g : E n → ℂ} (hg : Integrable g) (hc : Continuous g) (t : ℝ) (β : E n) :
    Integrable fun y => g y * chr t β y :=
  hg.norm.mono' (hc.mul (continuous_chr t β)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by rw [norm_mul, norm_chr, mul_one])

theorem ibp_dir {g : E n → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgi : Integrable g) (w : E n)
    (hgw : Integrable fun y => fderiv ℝ g y w) (t : ℝ) (β : E n) :
    ∫ y, fderiv ℝ g y w * chr t β y = -(lf t β w) * ∫ y, g y * chr t β y := by
  have hdiff : Differentiable ℝ g := hg.differentiable (by simp)
  have hcont : Continuous g := hg.continuous
  have hcw : Continuous fun y => fderiv ℝ g y w :=
    ((contDiff_infty_iff_fderiv.mp hg).2.continuous).clm_apply continuous_const
  have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := g) (g := chr t β) (v := w)
    (integrable_mul_chr hgw hcw t β)
    (by
      have : (fun y => g y * fderiv ℝ (chr t β) y w) = fun y => (g y * chr t β y) * lf t β w := by
        funext y; rw [fderiv_chr]; ring
      rw [this]
      exact (integrable_mul_chr hgi hcont t β).mul_const _)
    (integrable_mul_chr hgi hcont t β)
    (fun x _ => hdiff x) (fun x _ => differentiable_chr t β x)
  have : (fun y => g y * fderiv ℝ (chr t β) y w) = fun y => (g y * chr t β y) * lf t β w := by
    funext y; rw [fderiv_chr]; ring
  rw [this, integral_mul_const] at H
  linear_combination H

theorem ibp_dkl {g : E n → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgi : Integrable g) (k l : Fin n)
    (h1 : Integrable (Dkl k l g)) (h2 : Integrable (Dkl l k g)) (t : ℝ) (β : E n) :
    ∫ y, Dkl k l g y * chr t β y = -((-(Complex.I * t)) * herm β k l) * ∫ y, g y * chr t β y := by
  set u : E n := fun a b => (vkl k l a b).re
  set w : E n := fun a b => (vkl k l a b).im
  have hre : (fun y => fderiv ℝ g y u) = fun y => (Dkl k l g y + Dkl l k g y) / 2 := by
    funext y; rw [dkl_swap g k l y]; simp only [Dkl, dirC, u, w]; ring
  have him : (fun y => fderiv ℝ g y w) = fun y => (Dkl k l g y - Dkl l k g y) / (2 * Complex.I) := by
    funext y; rw [dkl_swap g k l y]; simp only [Dkl, dirC, u, w]; field_simp; ring
  have iu : Integrable fun y => fderiv ℝ g y u := by rw [hre]; exact (h1.add h2).div_const _
  have iw : Integrable fun y => fderiv ℝ g y w := by rw [him]; exact (h1.sub h2).div_const _
  have hcont := hg.continuous
  have hcu : Continuous fun y => fderiv ℝ g y u :=
    ((contDiff_infty_iff_fderiv.mp hg).2.continuous).clm_apply continuous_const
  have hcw : Continuous fun y => fderiv ℝ g y w :=
    ((contDiff_infty_iff_fderiv.mp hg).2.continuous).clm_apply continuous_const
  have eD : (fun y => Dkl k l g y * chr t β y) =
      fun y => fderiv ℝ g y u * chr t β y + Complex.I * (fderiv ℝ g y w * chr t β y) := by
    funext y; simp only [Dkl, dirC, u, w]; ring
  rw [eD, integral_add (integrable_mul_chr iu hcu t β) ((integrable_mul_chr iw hcw t β).const_mul _),
    integral_const_mul, ibp_dir hg hgi u iu t β, ibp_dir hg hgi w iw t β]
  have h := lf_re_im t β (vkl k l)
  rw [sum_vkl] at h
  linear_combination (-(∫ y, g y * chr t β y)) * h

theorem contDiff_foldr {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (L : List (Fin n × Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (L.foldr (fun kl g => Dkl kl.1 kl.2 g) f) := by
  induction L with
  | nil => simpa using hf
  | cons kl L ih => simpa using contDiff_dkl ih kl.1 kl.2

theorem ibp_list {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (β : E n)
    (hb : ∀ L : List (Fin n × Fin n), ∃ h : E n → ℝ, Integrable h ∧
      ∀ y, ‖L.foldr (fun kl g => Dkl kl.1 kl.2 g) f y‖ ≤ h y) (L : List (Fin n × Fin n)) :
    ∫ y, L.foldr (fun kl g => Dkl kl.1 kl.2 g) f y * chr t β y =
      (L.map fun kl => Complex.I * t * herm β kl.1 kl.2).prod * ∫ y, f y * chr t β y := by
  have hI : ∀ L : List (Fin n × Fin n), Integrable (L.foldr (fun kl g => Dkl kl.1 kl.2 g) f) := by
    intro L
    obtain ⟨h, hh, hbd⟩ := hb L
    exact integrable_of_bound (contDiff_foldr hf L).continuous hh hbd
  induction L with
  | nil => simp
  | cons kl L ih =>
    have h1 := hI (kl :: L)
    have h2 := hI ((kl.2, kl.1) :: L)
    simp only [List.foldr_cons] at h1 h2 ⊢
    rw [ibp_dkl (contDiff_foldr hf L) (hI L) kl.1 kl.2 h1 h2 t β, ih, List.map_cons, List.prod_cons]
    ring

theorem ibp : IBP := by
  intro n f t β hf ht hdet hb
  have hI : ∀ L : List (Fin n × Fin n), Integrable (L.foldr (fun kl g => Dkl kl.1 kl.2 g) f) := by
    intro L
    obtain ⟨h, hh, hbd⟩ := hb L
    exact integrable_of_bound (contDiff_foldr hf L).continuous hh hbd
  have hfold : ∀ σ : Equiv.Perm (Fin n), (List.finRange n).foldr (fun k g => Dkl k (σ k) g) f =
      ((List.finRange n).map fun k => (k, σ k)).foldr (fun kl g => Dkl kl.1 kl.2 g) f := by
    intro σ; rw [List.foldr_map]
  have hΔ : ∫ y, Delta f y * chr t β y = (Complex.I * t) ^ n * (herm β).det * ∫ y, f y * chr t β y := by
    have e : (fun y => Delta f y * chr t β y) = fun y => ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * (((List.finRange n).map fun k => (k, σ k)).foldr
          (fun kl g => Dkl kl.1 kl.2 g) f y * chr t β y) := by
      funext y
      simp only [Delta, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, hfold]
      refine Finset.sum_congr rfl fun σ _ => ?_
      ring
    rw [e, integral_finset_sum]
    swap
    · intro σ _
      exact (integrable_mul_chr (hI _) (contDiff_foldr hf _).continuous t β).const_mul _
    simp_rw [integral_const_mul, ibp_list hf t β hb, List.map_map]
    have hdet' : (herm β).det = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, herm β k (σ k) := by
      rw [← Matrix.det_transpose, Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      rfl
    rw [hdet', Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hp : (((List.finRange n).map ((fun kl : Fin n × Fin n => Complex.I * t * herm β kl.1 kl.2) ∘
        fun k => (k, σ k))).prod) = (Complex.I * t) ^ n * ∏ k, herm β k (σ k) := by
      rw [← Fin.prod_univ_def]
      simp only [Function.comp_apply]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hp]
    ring
  have hc : (Complex.I * t) ^ n ≠ 0 := pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ht))
  rw [hΔ]
  have e2 : (-(Complex.I * t)) ^ n = (-1) ^ n * (Complex.I * t) ^ n := by rw [neg_eq_neg_one_mul, mul_pow]
  rw [e2]
  have h1 : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by rw [← mul_pow]; norm_num
  field_simp

end PositivityTheory.Rg.Sw.WR.Ib

namespace PositivityTheory.Rg.Sw.WR

theorem ibp : IBP := Ib.ibp

end PositivityTheory.Rg.Sw.WR
