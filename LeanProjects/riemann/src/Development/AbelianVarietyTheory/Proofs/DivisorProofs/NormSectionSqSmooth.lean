import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.SmoothNormSq

theorem normSec_sq_smooth : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → A.Smooth (fun y => normSec L s y ^ 2) := by
  intro e X _ A L s hL hS j
  intro z0 hz0
  have hz0t : z0 ∈ (A.chart j).target := hz0.1
  set y0 := (A.chart j).symm z0 with hy0
  set V := (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U y0 with hV
  have hVo : IsOpen V := (A.chart j).isOpen_inter_preimage_symm (L.isOpen_U y0)
  have hz0V : z0 ∈ V := ⟨hz0t, L.mem_U y0⟩
  have hVn : V ∈ 𝓝 z0 := hVo.mem_nhds hz0V

  have hh : ContDiffAt ℝ ∞ (s y0 ∘ (A.chart j).symm) z0 :=
    by
    have h1 : ContDiffAt ℂ ∞ (s y0 ∘ (A.chart j).symm) z0 := (hS.1 y0 j z0 hz0V).contDiffAt
    exact h1.restrict_scalars ℝ
  have hφ : ContDiffAt ℝ ∞ (L.φ y0 ∘ (A.chart j).symm) z0 :=
    (hL.1 y0 j).contDiffAt hVn
  have hg : ContDiffAt ℝ ∞ (fun z => ‖(s y0 ∘ (A.chart j).symm) z‖ ^ 2 *
      Real.exp (-(L.φ y0 ∘ (A.chart j).symm) z) ^ 2) z0 := by
    refine ContDiffAt.mul ?_ ?_
    · exact ((contDiff_norm_sq ℝ).contDiffAt).comp z0 hh
    · exact ((Real.contDiff_exp.contDiffAt).comp z0 hφ.neg).pow 2
  have heq : (fun z => ‖(s y0 ∘ (A.chart j).symm) z‖ ^ 2 *
      Real.exp (-(L.φ y0 ∘ (A.chart j).symm) z) ^ 2) =ᶠ[𝓝 z0]
      ((fun y => normSec L s y ^ 2) ∘ (A.chart j).symm) := by
    filter_upwards [hVn] with z hz
    have h2 := hS.2 ((A.chart j).symm z) y0 ((A.chart j).symm z) ⟨L.mem_U _, hz.2⟩
    simp only [Function.comp_apply, normSec]
    rw [h2, mul_pow]
  exact (hg.congr_of_eventuallyEq heq.symm).contDiffWithinAt

end GlobalTheory.SmoothNormSq
