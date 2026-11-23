import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
open Set MeasureTheory
open scoped ContDiff Real Topology

namespace GlobalTheory.WeakHarmonicConv

theorem contDiff_dirDeriv {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (v : ℂ) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ f y v) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem laplacian_eq_dirDeriv {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (x : ℂ) :
    Laplacian.laplacian f x =
      fderiv ℝ (fun y => fderiv ℝ f y 1) x 1 +
        fderiv ℝ (fun y => fderiv ℝ f y Complex.I) x Complex.I := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have h : ∀ v : ℂ, fderiv ℝ (fun y => fderiv ℝ f y v) x v = fderiv ℝ (fderiv ℝ f) x v v := by
    intro v
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, h]
  simp

theorem dirDeriv_convolution (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) {u g : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (v : ℂ) :
    (fun y => fderiv ℝ (convolution u g L volume) y v) =
      convolution u (fun y => fderiv ℝ g y v) L volume := by
  funext x
  rw [(hc.hasFDerivAt_convolution_right L hu (hg.of_le (by simp)) x).fderiv,
    convolution_precompR_apply L hu (hc.fderiv ℝ) (hg.continuous_fderiv (by simp))]

theorem dirDeriv_comp_sub {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (x v : ℂ) :
    (fun y => fderiv ℝ (fun w => g (x - w)) y v) = fun y => - fderiv ℝ g (x - y) v := by
  funext y
  have h1 : HasFDerivAt (fun w : ℂ => x - w) (-(ContinuousLinearMap.id ℝ ℂ)) y :=
    (hasFDerivAt_id y).const_sub x
  have h2 := ((hg.differentiable (by simp)) (x - y)).hasFDerivAt.comp y h1
  have h3 : fderiv ℝ (fun w => g (x - w)) y = _ := h2.fderiv
  rw [h3]
  simp

theorem dirDeriv_two_comp_sub {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (x v y : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ (fun w => g (x - w)) y v) y v =
      fderiv ℝ (fun y => fderiv ℝ g y v) (x - y) v := by
  rw [dirDeriv_comp_sub hg, fderiv_fun_neg]
  have := congrFun (dirDeriv_comp_sub (contDiff_dirDeriv hg v) x v) y
  simp only [neg_apply]
  rw [this, neg_neg]

theorem harmonicOnNhd_convolution (u : ℂ → ℝ) (hu : Continuous u)
    (hw : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ w : ℂ, u w * Laplacian.laplacian φ w = 0)
    (ψ : ℂ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    InnerProductSpace.HarmonicOnNhd
      (MeasureTheory.convolution ψ u (ContinuousLinearMap.lsmul ℝ ℝ) volume) univ := by
  have hl : LocallyIntegrable u volume := hu.locallyIntegrable
  have hs : ContDiff ℝ ∞ (MeasureTheory.convolution ψ u (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hc.contDiff_convolution_left _ hψ hl
  intro x₀ _
  refine ⟨(hs.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).contDiffAt, Filter.Eventually.of_forall fun x => ?_⟩
  rw [laplacian_eq_dirDeriv hs, ← convolution_flip]
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := (ContinuousLinearMap.lsmul ℝ ℝ).flip with hL
  have key : ∀ v : ℂ, fderiv ℝ (fun y => fderiv ℝ (convolution u ψ L volume) y v) x v =
      convolution u (fun y => fderiv ℝ (fun y => fderiv ℝ ψ y v) y v) L volume x := by
    intro v
    rw [dirDeriv_convolution L hl hψ hc v]
    exact congrFun (dirDeriv_convolution L hl (contDiff_dirDeriv hψ v) (hc.fderiv_apply ℝ v) v) x
  have hex : ∀ v : ℂ, ConvolutionExistsAt u
      (fun y => fderiv ℝ (fun y => fderiv ℝ ψ y v) y v) x L volume := fun v =>
    ((hc.fderiv_apply ℝ v).fderiv_apply ℝ v).convolutionExists_right L hl
      (contDiff_dirDeriv (contDiff_dirDeriv hψ v) v).continuous x
  have hφ : ContDiff ℝ ∞ (fun w => ψ (x - w)) := hψ.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport (fun w => ψ (x - w)) :=
    hc.comp_homeomorph (Homeomorph.subLeft x)
  have h0 := hw _ hφ hφc
  rw [key, key, convolution_def, convolution_def, ← integral_add (hex 1) (hex Complex.I)]
  refine Eq.trans ?_ h0
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [laplacian_eq_dirDeriv hφ, dirDeriv_two_comp_sub hψ, hL]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  ring

end GlobalTheory.WeakHarmonicConv
