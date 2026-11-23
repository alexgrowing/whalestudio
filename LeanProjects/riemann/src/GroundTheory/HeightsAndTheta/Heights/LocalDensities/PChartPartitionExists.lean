import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeIntB
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsChartPartition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm.M Set
open scoped ContDiff Manifold

theorem ChartPartitionExists.proof : ChartPartitionExists.Statement := by
  intro e X _ _ A
  classical
  let _ : ChartedSpace (Fin e → ℂ) X :=
    { atlas := Set.range A.chart
      chartAt := fun x => A.chart (A.cover x).choose
      mem_chart_source := fun x => (A.cover x).choose_spec
      chart_mem_atlas := fun x => ⟨_, rfl⟩ }
  have : IsManifold 𝓘(ℝ, Fin e → ℂ) ∞ X := by
    apply isManifold_of_contDiffOn
    rintro _ _ ⟨j, rfl⟩ ⟨k, rfl⟩
    have h := A.holo j k
    have hs : ((A.chart j).symm ≫ₕ A.chart k).source =
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := by
      simp
    have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
      (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
        (A.chart k).open_source
    have hc : ContDiffOn ℂ ∞ (A.chart k ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
      h.contDiffOn ho.uniqueDiffOn
    simpa [hs] using hc.restrict_scalars ℝ
  have : SecondCountableTopology X := ReciprocityTheory.AnForm.M.dI_secondCountable A
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (Fin e → ℂ) X
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin e → ℂ) isClosed_univ
    (fun j => (A.chart j).source) (fun j => (A.chart j).open_source)
    (fun x _ => mem_iUnion.2 (A.cover x))
  refine ⟨⟨fun j => f j, fun k j => ?_, fun j x => f.nonneg j x, fun j => hf j, fun x => ?_⟩⟩
  · have hmem : A.chart j ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin e → ℂ) ∞ X :=
      IsManifold.subset_maximalAtlas ⟨j, rfl⟩
    have h1 : ContMDiffOn 𝓘(ℝ, Fin e → ℂ) 𝓘(ℝ) ∞ (f k) (A.chart j).source :=
      (f k).contMDiff.contMDiffOn
    rw [contMDiffOn_iff_source_of_mem_maximalAtlas hmem subset_rfl,
      contMDiffOn_iff_contDiffOn] at h1
    simpa [(A.chart j).image_source_eq_target] using h1
  · rw [← finsum_eq_sum_of_fintype]
    exact f.sum_eq_one (mem_univ x)

end GroundTheory.Heights₂.Heights.FourB
