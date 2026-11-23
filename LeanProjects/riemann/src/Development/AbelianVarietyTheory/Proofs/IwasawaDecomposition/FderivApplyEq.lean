import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BetaLowerAndSmul

open Formalism.DegreeFormula GlobalTheory.HodgeDomain
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HessForm

variable {ι : Type} [Fintype ι] {p q : ℕ}

abbrev Fl (ι : Type) (p q : ℕ) : Type := ι × Fin p × Fin q → ℂ

theorem flat_add (ξ ζ : Pt ι p q) : flat (ξ + ζ) = flat ξ + flat ζ := rfl

theorem flat_smul (c : ℂ) (ξ : Pt ι p q) :
    flat (c • ξ) = c.re • flat ξ + c.im • flat (Complex.I • ξ) := by
  funext x
  simp only [flat, Pi.add_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im c]
  ring

theorem flat_I_smul (c : ℂ) (ξ : Pt ι p q) :
    flat (Complex.I • c • ξ) = c.re • flat (Complex.I • ξ) - c.im • flat ξ := by
  funext x
  simp only [flat, Pi.sub_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im c]
  linear_combination (c.im * ξ x.1 x.2.1 x.2.2) * Complex.I_mul_I

def fn (B : Fl ι p q →L[ℝ] Fl ι p q →L[ℝ] ℝ) (ξ ζ : Pt ι p q) : ℂ :=
  (((B (flat ξ) (flat ζ) + B (flat (Complex.I • ξ)) (flat (Complex.I • ζ)) : ℝ) : ℂ) +
    Complex.I * ((B (flat ξ) (flat (Complex.I • ζ)) - B (flat (Complex.I • ξ)) (flat ζ) : ℝ) : ℂ)) /
      (4 * Real.pi)

def sesq (B : Fl ι p q →L[ℝ] Fl ι p q →L[ℝ] ℝ) : Pt ι p q →ₗ[ℂ] Pt ι p q →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fn B)
    (fun ξ ξ' ζ => by
      simp only [fn, smul_add, flat_add, map_add, ContinuousLinearMap.add_apply]
      push_cast; ring)
    (fun c ξ ζ => by
      simp only [fn]
      rw [flat_I_smul c ξ, flat_smul c ξ]
      simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
      conv_rhs => rw [← Complex.re_add_im c]
      push_cast
      ring_nf; simp only [Complex.I_sq]; ring)
    (fun ξ ζ ζ' => by
      simp only [fn, smul_add, flat_add, map_add]
      push_cast; ring)
    (fun c ξ ζ => by
      simp only [fn]
      rw [flat_I_smul c ζ, flat_smul c ζ]
      simp only [map_add, map_sub, map_smul, smul_eq_mul]
      conv_rhs => rw [← Complex.re_add_im c]
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring_nf; simp only [Complex.I_sq]; ring)

end GlobalTheory.HessForm

namespace GlobalTheory.HessForm

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem sesq_apply (B : Fl ι p q →L[ℝ] Fl ι p q →L[ℝ] ℝ) (ξ ζ : Pt ι p q) : sesq B ξ ζ = fn B ξ ζ := rfl

theorem re_sesq_self (B : Fl ι p q →L[ℝ] Fl ι p q →L[ℝ] ℝ) (ξ : Pt ι p q) :
    (sesq B ξ ξ).re = (B (flat ξ) (flat ξ) + B (flat (Complex.I • ξ)) (flat (Complex.I • ξ))) / (4 * Real.pi) := by
  rw [sesq_apply, fn, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_re]
  simp

theorem sesq_herm {B : Fl ι p q →L[ℝ] Fl ι p q →L[ℝ] ℝ} (hB : ∀ u v, B u v = B v u) (ξ ζ : Pt ι p q) :
    sesq B ζ ξ = starRingEnd ℂ (sesq B ξ ζ) := by
  simp only [sesq_apply, fn, map_div₀, map_add, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  rw [hB (flat ζ), hB (flat (Complex.I • ζ)), hB (flat ζ) (flat (Complex.I • ξ)), hB (flat (Complex.I • ζ)) (flat ξ)]
  push_cast; ring

theorem ext_of_re {a b : Pt ι p q →ₗ[ℂ] Pt ι p q →ₗ⋆[ℂ] ℂ} (ha : ∀ ξ ζ, a ζ ξ = starRingEnd ℂ (a ξ ζ))
    (hb : ∀ ξ ζ, b ζ ξ = starRingEnd ℂ (b ξ ζ)) (h : ∀ ξ, (a ξ ξ).re = (b ξ ξ).re) : a = b := by
  have e : ∀ ξ, (a - b) ξ ξ = 0 := fun ξ => sub_eq_zero.2 (Complex.ext (h ξ)
    ((Complex.conj_eq_iff_im.1 (ha ξ ξ).symm).trans (Complex.conj_eq_iff_im.1 (hb ξ ξ).symm).symm))
  rw [← sub_eq_zero]
  generalize a - b = c at e
  refine LinearMap.ext₂ fun ξ ζ => ?_
  have e1 := e (ξ + ζ)
  have e2 := e (ξ + Complex.I • ζ)
  simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, e, smul_eq_mul, Complex.conj_I,
    RingHom.id_apply] at e1 e2
  show c ξ ζ = 0
  linear_combination (1 / 2) * e1 + (Complex.I / 2) * e2 + ((c ξ ζ - c ζ ξ) / 2) * Complex.I_mul_I

abbrev hess (F : Fl ι p q → ℝ) (x : Fl ι p q) : Fl ι p q →L[ℝ] Fl ι p q →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ F) x

theorem fderiv_apply_eq {F : Fl ι p q → ℝ} {x : Fl ι p q} (hF : ContDiffAt ℝ 2 F x) (a b : Fl ι p q) :
    fderiv ℝ (fun v => fderiv ℝ F v a) x b = hess F x b a := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const a)]
  simp

theorem hess_symm {F : Fl ι p q → ℝ} {x : Fl ι p q} (hF : ContDiffAt ℝ 2 F x) (u v : Fl ι p q) :
    hess F x u v = hess F x v u :=
  hF.isSymmSndFDerivAt (by simp) u v

theorem ddc_eq_sesq {f : Pt ι p q → ℝ} {z : Pt ι p q} (hf : ContDiffAt ℝ 2 (fun v => f (unflat v)) (flat z))
    (ξ : Pt ι p q) : ddc f z ξ = (sesq (hess (fun v => f (unflat v)) (flat z)) ξ ξ).re := by
  rw [GlobalTheory.PoincareLower.ddc_eq hf, re_sesq_self, fderiv_apply_eq hf, fderiv_apply_eq hf]

theorem contDiffOn_sesq {G : Fl ι p q → ℝ} {U : Set (Fl ι p q)} (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U)
    (ξ ζ : Pt ι p q) : ContDiffOn ℝ ∞ (fun v => sesq (hess G v) ξ ζ) U := by
  have h1 : ContDiffOn ℝ ∞ (fun v => fderiv ℝ G v) U := hG.fderiv_of_isOpen hU (by simp)
  have h2 : ContDiffOn ℝ ∞ (fun v => hess G v) U := h1.fderiv_of_isOpen hU (by simp)
  have ap : ∀ a b : Fl ι p q, ContDiffOn ℝ ∞ (fun v => ((hess G v a b : ℝ) : ℂ)) U := fun a b =>
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((h2.clm_apply contDiffOn_const).clm_apply contDiffOn_const)
  simp only [sesq_apply, fn]
  push_cast
  exact ((((ap _ _).add (ap _ _)).add (contDiffOn_const.mul ((ap _ _).sub (ap _ _)))).div_const _)

end GlobalTheory.HessForm
