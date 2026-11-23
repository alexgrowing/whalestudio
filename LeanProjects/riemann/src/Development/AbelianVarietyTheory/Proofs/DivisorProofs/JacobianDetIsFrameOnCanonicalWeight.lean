import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLoc
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem jdet_isFrameOn_kap : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → A.IsFrameOn A.kap U (jdet A z) := by
  intro n Y _ _ _ _ _ ι La _ A U z hz
  refine ⟨⟨fun i => ?_, fun i j y hy hi hj => ?_⟩, fun y hy => hz.det_ne _ y hy (A.mem_pick y)⟩
  · set S := (A.chart i).target ∩ (A.chart i).symm ⁻¹' U with hS
    have hSo : IsOpen S := (A.chart i).isOpen_inter_preimage_symm hz.isOpen
    have hk : ∀ k, ContDiffOn ℂ ∞ (fun v => (z ((A.chart i).symm v)) k) S := fun k =>
      contDiffOn_of_differentiableOn n _ S hSo (fun v hv =>
        (EuclideanSpace.proj k : V n →L[ℂ] ℂ).differentiableAt.comp_differentiableWithinAt v
          (hz.holo i v hv))
    have hpi := contDiffOn_pi.mpr hk
    have h1 : ContDiffOn ℂ ∞ (z ∘ (A.chart i).symm) S :=
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.contDiff.comp_contDiffOn hpi
    have h2 : ContDiffOn ℂ ∞ (fderiv ℂ (z ∘ (A.chart i).symm)) S :=
      h1.fderiv_of_isOpen hSo (by simp)
    have h3 : DifferentiableOn ℂ (fun v => (fderiv ℂ (z ∘ (A.chart i).symm) v).det) S := by
      intro v hv
      exact ((flL_det_contDiffAt ((h2 v hv).contDiffAt (hSo.mem_nhds hv))).differentiableAt
        (by simp)).differentiableWithinAt
    refine h3.congr fun v hv => ?_
    simp only [Function.comp_apply, jdet, jz, (A.chart i).right_inv hv.1]
  · have hyt : A.chart i y ∈ (A.chart i).target := (A.chart i).map_source hi
    have hov : IsOpen (ovl A.chart i j) :=
      (A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source
    have hmov : A.chart i y ∈ ovl A.chart i j := ⟨hyt, by simp [(A.chart i).left_inv hi, hj]⟩
    have hτ : DifferentiableAt ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y) :=
      (A.holo_trans i j).differentiableAt (hov.mem_nhds hmov)
    have hτy : (A.chart j ∘ (A.chart i).symm) (A.chart i y) = A.chart j y := by
      simp [(A.chart i).left_inv hi]
    have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
      (A.chart j).isOpen_inter_preimage_symm hz.isOpen
    have hmj : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
      ⟨(A.chart j).map_source hj, by simp [(A.chart j).left_inv hj, hy]⟩
    have hzj : DifferentiableAt ℂ (z ∘ (A.chart j).symm) ((A.chart j ∘ (A.chart i).symm) (A.chart i y)) := by
      rw [hτy]; exact (hz.holo j).differentiableAt (hSo.mem_nhds hmj)
    have hev : z ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i y)]
        (z ∘ (A.chart j).symm) ∘ (A.chart j ∘ (A.chart i).symm) := by
      filter_upwards [hov.mem_nhds hmov] with v hv
      simp only [Function.comp_apply, (A.chart j).left_inv hv.2]
    have hjz : jz A z i y = (jz A z j y).comp (fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y)) := by
      unfold jz
      rw [hev.fderiv_eq, fderiv_comp _ hzj hτ, hτy]
    simp only [jdet]
    rw [hjz, A.g_kap i j y hi hj]
    exact (LinearMap.det_comp _ _).trans (mul_comm _ _)

end GlobalTheory.OTY
