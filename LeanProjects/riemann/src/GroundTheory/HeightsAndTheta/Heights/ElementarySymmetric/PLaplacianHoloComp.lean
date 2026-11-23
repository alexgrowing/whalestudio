import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsLaplacianHoloComp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian Filter Topology

theorem fderiv_fderiv_comp_holo_apply (φ : ℂ → ℝ) (T : ℂ → ℂ) (t : ℂ)
    (hφ : ContDiffAt ℝ 2 φ (T t)) (hT : AnalyticAt ℂ T t) (v : ℂ) :
    fderiv ℝ (fderiv ℝ (φ ∘ T)) t v v =
      fderiv ℝ (fderiv ℝ φ) (T t) (deriv T t * v) (deriv T t * v) +
        fderiv ℝ φ (T t) (deriv (deriv T) t * v * v) := by

  set A : ℂ → ℂ →L[ℝ] ℂ := fun s => ContinuousLinearMap.lsmul ℝ ℂ (deriv T s) with hAdef
  have hTev : ∀ᶠ s in 𝓝 t, AnalyticAt ℂ T s := hT.eventually_analyticAt
  have hφev : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 2 φ (T s) :=
    hT.continuousAt.tendsto.eventually (hφ.eventually (by simp))
  have hfd : fderiv ℝ (φ ∘ T) =ᶠ[𝓝 t] fun s => (fderiv ℝ φ (T s)).comp (A s) := by
    filter_upwards [hTev, hφev] with s hs hs'
    have h1 : HasFDerivAt T
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv T s)).restrictScalars ℝ) s :=
      hs.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
    have h2 := (hs'.differentiableAt (by norm_num)).hasFDerivAt.comp s h1
    rw [h2.fderiv]
    congr 1
    ext w
    simp [hAdef, mul_comm]

  have hT1 : HasFDerivAt T
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv T t)).restrictScalars ℝ) t :=
    hT.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hc : HasFDerivAt (fun s => fderiv ℝ φ (T s))
      ((fderiv ℝ (fderiv ℝ φ) (T t)).comp
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv T t)).restrictScalars ℝ)) t := by
    have hd : DifferentiableAt ℝ (fderiv ℝ φ) (T t) :=
      (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact hd.hasFDerivAt.comp t hT1

  have hT2 : HasFDerivAt (deriv T)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv (deriv T) t)).restrictScalars ℝ) t :=
    hT.deriv.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hA : HasFDerivAt A ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ).comp
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv (deriv T) t)).restrictScalars ℝ)) t :=
    (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ).hasFDerivAt.comp t hT2
  have hG := hc.clm_comp hA
  rw [hfd.fderiv_eq, hG.fderiv]
  simp [hAdef, mul_comm]
  ring

theorem LaplacianHoloComp.full : LaplacianHoloComp.Statement := by
  intro φ T t hφ hT
  have hsymm := hφ.isSymmSndFDerivAt (by simp)
  rw [laplacian_eq_iteratedFDeriv_complexPlane, laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_fderiv_comp_holo_apply φ T t hφ hT, fderiv_fderiv_comp_holo_apply φ T t hφ hT]
  set D := fderiv ℝ (fderiv ℝ φ) (T t)
  set w := deriv T t
  have hcancel : fderiv ℝ φ (T t) (deriv (deriv T) t * 1 * 1) +
      fderiv ℝ φ (T t) (deriv (deriv T) t * Complex.I * Complex.I) = 0 := by
    rw [← map_add]
    have : deriv (deriv T) t * 1 * 1 + deriv (deriv T) t * Complex.I * Complex.I = 0 := by
      rw [mul_assoc _ Complex.I, Complex.I_mul_I]; ring
    rw [this, map_zero]
  have hw : w * 1 = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have hwI : w * Complex.I = (-w.im : ℝ) • (1 : ℂ) + (w.re : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have hs : D 1 Complex.I = D Complex.I 1 := hsymm 1 Complex.I
  have hn : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hw, hwI, hn]
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul]
  linear_combination hcancel + (w.re * w.im - w.im * w.re) * hs
