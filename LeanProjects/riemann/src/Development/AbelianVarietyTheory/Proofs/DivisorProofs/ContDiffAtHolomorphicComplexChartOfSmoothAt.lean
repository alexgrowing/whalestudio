import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem contDiffAt_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ}, y ∈ e.source → CInfAt f y → ContDiffAt ℝ ∞ (fun v => f (e.symm v)) (e y) := by
  intro F _ σ X e he f y hy hf
  obtain ⟨W, ι, hι, g, Φ, O, hyW, hO, hgO, hΦ, hfeq⟩ := hf

  have hU : IsOpen (e.target ∩ e.symm ⁻¹' ptsIn X.str σ W) :=
    e.isOpen_inter_preimage_symm (GlobalTheory.CxPts.isOpen_ptsIn W)
  have hyU : e y ∈ e.target ∩ e.symm ⁻¹' ptsIn X.str σ W :=
    ⟨e.map_source hy, by rw [Set.mem_preimage, e.left_inv hy]; exact hyW⟩

  have hGc : ContDiffAt ℂ ∞ (fun v a => GlobalTheory.CxPts.ev X.str σ W (g a) (e.symm v)) (e y) := by
    rw [contDiffAt_pi]
    intro a
    exact (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ hU (he W (g a))).contDiffAt
      (hU.mem_nhds hyU)

  have hΦc : ContDiffAt ℝ ∞ Φ (fun a => GlobalTheory.CxPts.ev X.str σ W (g a) (e.symm (e y))) := by
    rw [e.left_inv hy]
    exact hΦ.contDiffAt (hO.mem_nhds hgO)
  have hcomp : ContDiffAt ℝ ∞ (fun v => Φ fun a => GlobalTheory.CxPts.ev X.str σ W (g a) (e.symm v)) (e y) :=
    hΦc.comp (e y) (hGc.restrict_scalars ℝ)
  refine hcomp.congr_of_eventuallyEq ?_

  have ht : Filter.Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    have h := e.continuousAt_symm (e.map_source hy)
    rw [ContinuousAt, e.left_inv hy] at h
    exact h
  exact ht.eventually hfeq

end GlobalTheory.GoodTop
