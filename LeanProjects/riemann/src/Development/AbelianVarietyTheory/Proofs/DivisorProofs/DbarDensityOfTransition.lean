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

theorem clm_single_eq_det_smul (L : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) :
    L (EuclideanSpace.single 0 1) = L.det • EuclideanSpace.single 0 1 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 1) ℂ).toBasis,
    Matrix.det_unique]
  ext i
  simp [LinearMap.toMatrix_apply, Subsingleton.elim i 0]

theorem det_eq_apply_single (L : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) :
    L.det = L (EuclideanSpace.single 0 1) 0 := by
  rw [clm_single_eq_det_smul]; simp

theorem isDens_re_dbar_coeff : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (m : AlgChart p σ 1 → CxPts p σ → ℂ),
    (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) →
    (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
      m c y = ChartGlue.transDet c.e c'.e y * m c' y) →
    IsDens (fun (c : AlgChart p σ 1) (y : CxPts p σ) =>
      (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re) := by
  intro k _ X p σ m hC hT
  refine ⟨fun c c' y hy hy' => ?_, fun c => ?_⟩
  · show (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re =
      ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 *
        (dbar (fun v => m c' (c'.e.symm v)) (c'.e y) (EuclideanSpace.single 0 1)).re
    have ho := ChartGlue.isOpen_over c.e c'.e.open_source
    have hm := ho.mem_nhds (ChartGlue.mem_over c.e hy hy')
    have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
    have hτ : DifferentiableAt ℂ (c'.e ∘ c.e.symm) (c.e y) := (c.holo_trans c').differentiableAt hm
    have hτC : ContDiffAt ℂ 2 (c'.e ∘ c.e.symm) (c.e y) :=
      contDiffAt_euclidean.2 fun i =>
        ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn 1 _ _ ho
          (differentiableOn_euclidean.1 (c.holo_trans c') i)).contDiffAt hm).of_le (by norm_cast)
    have hdd : DifferentiableAt ℂ (fun v => (fderiv ℂ (c'.e ∘ c.e.symm) v).det) (c.e y) := by
      have h1 : DifferentiableAt ℂ (fderiv ℂ (c'.e ∘ c.e.symm)) (c.e y) :=
        (hτC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
      have : (fun v => (fderiv ℂ (c'.e ∘ c.e.symm) v).det) =
          fun v => fderiv ℂ (c'.e ∘ c.e.symm) v (EuclideanSpace.single 0 1) 0 :=
        funext fun v => det_eq_apply_single _
      rw [this]
      exact (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℂ (Fin 1) →L[ℂ] ℂ).differentiableAt.comp _
        (h1.clm_apply (differentiableAt_const _))
    have hg : DifferentiableAt ℝ (fun v => m c' (c'.e.symm v)) ((c'.e ∘ c.e.symm) (c.e y)) := by
      rw [e₂]; exact (hC c' y hy').differentiableAt one_ne_zero
    have hgτ : DifferentiableAt ℝ (fun v => m c' (c'.e.symm ((c'.e ∘ c.e.symm) v))) (c.e y) :=
      hg.comp (f := c'.e ∘ c.e.symm) _ (hτ.restrictScalars ℝ)
    have hfe : (fun v => m c (c.e.symm v)) =ᶠ[𝓝 (c.e y)]
        fun v => (fderiv ℂ (c'.e ∘ c.e.symm) v).det * m c' (c'.e.symm ((c'.e ∘ c.e.symm) v)) := by
      filter_upwards [hm] with v hv
      rw [hT c c' _ (c.e.map_target hv.1) hv.2, ChartGlue.transDet, c.e.right_inv hv.1,
        Function.comp_apply, c'.e.left_inv hv.2]
    rw [dbar_congr hfe, dbar_mul (hdd.restrictScalars ℝ) hgτ, dbar_eq_zero hdd,
      ContinuousLinearMap.zero_apply, zero_mul, add_zero,
      dbar_comp_holo (u := fun v => m c' (c'.e.symm v)) hg hτ, clm_single_eq_det_smul,
      ContinuousLinearMap.map_smulₛₗ, e₂, smul_eq_mul, ← mul_assoc, Complex.mul_conj',
      ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    rfl
  · have hcont : ContinuousOn (fun v => (dbar (fun v => m c (c.e.symm v)) v
        (EuclideanSpace.single 0 1)).re) c.e.target := by
      intro v hv
      have h1 := hC c (c.e.symm v) (c.e.map_target hv)
      rw [c.e.right_inv hv] at h1
      have h2 : ContinuousAt (fun w => fderiv ℝ (fun v => m c (c.e.symm v)) w) v :=
        (h1.fderiv_right (m := 0) (by norm_num)).continuousAt
      refine ContinuousAt.continuousWithinAt ?_
      have h3 : (fun w => (dbar (fun v => m c (c.e.symm v)) w (EuclideanSpace.single 0 1)).re) =
          fun w => ((1 / 2 : ℂ) • (fderiv ℝ (fun v => m c (c.e.symm v)) w (EuclideanSpace.single 0 1) +
            Complex.I • fderiv ℝ (fun v => m c (c.e.symm v)) w
              (Complex.I • EuclideanSpace.single 0 1))).re :=
        funext fun w => by rw [dbar_apply]
      rw [h3]
      have h4 : ContinuousAt (fun w => fderiv ℝ (fun v => m c (c.e.symm v)) w
          (EuclideanSpace.single 0 1)) v := h2.clm_apply continuousAt_const
      have h5 : ContinuousAt (fun w => fderiv ℝ (fun v => m c (c.e.symm v)) w
          (Complex.I • EuclideanSpace.single 0 1)) v := h2.clm_apply continuousAt_const
      exact Complex.continuous_re.continuousAt.comp ((h4.add (h5.const_smul Complex.I)).const_smul
        (1 / 2 : ℂ))
    exact hcont.congr fun v hv => by simp only [c.e.right_inv hv]

end GlobalTheory.CurveDens
