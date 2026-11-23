import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.MixDens

theorem antilin_apply_eq_sum {D : ℕ} (L : EuclideanSpace ℂ (Fin D) →L⋆[ℂ] ℂ) (w : EuclideanSpace ℂ (Fin D)) :
    L w = ∑ b, star (w b) * L (EuclideanSpace.single b 1) := by
  have h : w = ∑ b, w b • EuclideanSpace.single b (1 : ℂ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h]
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ContinuousLinearMap.map_smulₛₗ, smul_eq_mul]
  rfl

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem dbar_coeff_chg (α : AlgChart p σ D → CxPts p σ → Fin D → ℂ)
    (hC : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ∀ j, ContDiffAt ℝ 1 (fun v => α c (c.e.symm v) j) (c.e y))
    (hT : ∀ (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
      ∀ j, α c y j = ∑ a, transMat c c' y a j * α c' y a)
    (c c' : AlgChart p σ D) (y : CxPts p σ) (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) :
    (Matrix.of fun j l => dbar (fun v => α c (c.e.symm v) j) (c.e y) (EuclideanSpace.single l 1)) =
      chg (transMat c c' y)
        (Matrix.of fun j l => dbar (fun v => α c' (c'.e.symm v) j) (c'.e y) (EuclideanSpace.single l 1)) := by
  have ho := ChartGlue.isOpen_over c.e c'.e.open_source
  have hm := ho.mem_nhds (ChartGlue.mem_over c.e hy hy')
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  have hτ : DifferentiableAt ℂ (c'.e ∘ c.e.symm) (c.e y) := (c.holo_trans c').differentiableAt hm
  have hτC : ContDiffAt ℂ 2 (c'.e ∘ c.e.symm) (c.e y) :=
    contDiffAt_euclidean.2 fun i =>
      ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho
        (differentiableOn_euclidean.1 (c.holo_trans c') i)).contDiffAt hm).of_le (by norm_cast)
  have hdd (a j : Fin D) : DifferentiableAt ℂ
      (fun v => fderiv ℂ (c'.e ∘ c.e.symm) v (EuclideanSpace.single j 1) a) (c.e y) := by
    have h1 : DifferentiableAt ℂ (fderiv ℂ (c'.e ∘ c.e.symm)) (c.e y) :=
      (hτC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact (EuclideanSpace.proj a : EuclideanSpace ℂ (Fin D) →L[ℂ] ℂ).differentiableAt.comp _
      (h1.clm_apply (differentiableAt_const _))
  have hg (a : Fin D) : DifferentiableAt ℝ (fun v => α c' (c'.e.symm v) a) ((c'.e ∘ c.e.symm) (c.e y)) := by
    rw [e₂]; exact (hC c' y hy' a).differentiableAt one_ne_zero
  have hgτ (a : Fin D) :
      DifferentiableAt ℝ (fun v => α c' (c'.e.symm ((c'.e ∘ c.e.symm) v)) a) (c.e y) :=
    (hg a).comp (f := c'.e ∘ c.e.symm) _ (hτ.restrictScalars ℝ)
  ext j l
  have hfe : (fun v => α c (c.e.symm v) j) =ᶠ[𝓝 (c.e y)]
      fun v => ∑ a, fderiv ℂ (c'.e ∘ c.e.symm) v (EuclideanSpace.single j 1) a *
        α c' (c'.e.symm ((c'.e ∘ c.e.symm) v)) a := by
    filter_upwards [hm] with v hv
    rw [hT c c' _ (c.e.map_target hv.1) hv.2]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [transMat, of_apply, c.e.right_inv hv.1, Function.comp_apply, c'.e.left_inv hv.2]
  rw [of_apply, dbar_congr hfe, dbar_sum fun a _ => ((hdd a j).restrictScalars ℝ).fun_mul (hgτ a),
    ContinuousLinearMap.sum_apply, chg]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dbar_mul ((hdd a j).restrictScalars ℝ) (hgτ a), dbar_eq_zero (hdd a j),
    ContinuousLinearMap.zero_apply, zero_mul, add_zero,
    dbar_comp_holo (u := fun v => α c' (c'.e.symm v) a) (hg a) hτ, e₂, antilin_apply_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [transpose_apply, conjTranspose_apply, transMat, of_apply]
  ring

theorem isDens_mix_dbar : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) (A : AlgChart p σ (d + 1) → CxPts p σ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (α : AlgChart p σ (d + 1) → CxPts p σ → Fin (d + 1) → ℂ), IsForm A → (∀ c : AlgChart p σ (d + 1), ∀ y ∈ c.e.source, ∀ j, ContDiffAt ℝ 1 (fun v => α c (c.e.symm v) j) (c.e y)) → (∀ (c c' : AlgChart p σ (d + 1)) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → ∀ j, α c y j = ∑ a, transMat c c' y a j * α c' y a) → IsDens fun (c : AlgChart p σ (d + 1)) y => mix d (A c y) (Matrix.of fun j l => dbar (fun v => α c (c.e.symm v) j) (c.e y) (EuclideanSpace.single l 1)) := by
  intro k _ X p σ d A α hA hC hT
  refine ⟨fun c c' y hy hy' => ?_, fun c => ?_⟩
  · beta_reduce
    rw [hA.1 c c' y hy hy', dbar_coeff_chg α hC hT c c' y hy hy', mix_chg, det_transMat]
  · have hc : Continuous fun x : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ × Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
        mix d x.1 x.2 :=
      continuous_const.mul (Complex.continuous_re.comp
        (continuous_fst.matrix_adjugate.matrix_mul continuous_snd).matrix_trace)
    have hN : ContinuousOn (fun v => (Matrix.of fun j l =>
        dbar (fun w => α c (c.e.symm w) j) v (EuclideanSpace.single l 1) :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) c.e.target := by
      refine continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => fun v hv => ?_
      have h1 := hC c (c.e.symm v) (c.e.map_target hv) j
      rw [c.e.right_inv hv] at h1
      have h2 : ContinuousAt (fun w => fderiv ℝ (fun v => α c (c.e.symm v) j) w) v :=
        (h1.fderiv_right (m := 0) (by norm_num)).continuousAt
      have h4 := h2.clm_apply (continuousAt_const (y := EuclideanSpace.single l (1 : ℂ)))
      have h5 := h2.clm_apply (continuousAt_const (y := Complex.I • EuclideanSpace.single l (1 : ℂ)))
      exact ((h4.add (h5.const_smul Complex.I)).const_smul (1 / 2 : ℂ)).continuousWithinAt
    refine (Continuous.comp_continuousOn (f := fun v => (A c (c.e.symm v), _)) hc
      ((hA.2.1 c).prodMk hN)).congr fun v hv => ?_
    simp only [Function.comp_apply, c.e.right_inv hv]

end GlobalTheory.MixDens
