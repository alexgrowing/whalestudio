import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Partition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open scoped ContDiff

noncomputable section

theorem BdPartition.proof : BdPartition.Statement := by
  intro X _ _ _ D A R
  set e : Fin R.n → OpenPartialHomeomorph X (Fin D → ℂ) :=
    fun j => (R.ψ j).restrOpen (bdDom R j) (isOpen_bdDom R j) with he
  have hsrc : ∀ j, (e j).source = bdDom R j := by
    intro j
    simp only [he, OpenPartialHomeomorph.restrOpen_source]
    exact Set.inter_eq_right.2 Set.inter_subset_left
  have hc : ∀ j, IsCompatChart A (e j) := fun j =>
    ReciprocityTheory.AnForm.M.pa_compat_restr A (R.ψ j) (R.compat j) _ (isOpen_bdDom R j)
  have hcov : ∀ x, ∃ j, x ∈ (e j).source := fun x =>
    ⟨bdIdx R x, by rw [hsrc]; exact mem_bdDom_bdIdx R x⟩
  have htr : ∀ i j, ContDiffOn ℝ ∞ (e j ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' (e j).source) := fun i j =>
    ReciprocityTheory.AnForm.M.pa_holoSmooth _ _ fun v hv =>
      ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.compat_trans A (hc i) (hc j) hv.1 hv.2
  obtain ⟨χ, h0, h1, hs, hsm⟩ := ReciprocityTheory.AnForm.exists_chart_partition e hcov htr
  obtain ⟨B, hAB, -, hB⟩ := ReciprocityTheory.AnForm.M.atlasOfCompat A e hc hcov
  have hBs : ∀ i, B.Smooth (χ i) := by
    intro i j
    obtain ⟨l, hl⟩ := hB j
    rw [hl]
    exact (hsm i l).mono Set.inter_subset_left
  refine ⟨χ, fun i => ReciprocityTheory.AnForm.M.smoothOn_of_compatible hAB.symm' isOpen_univ (hBs i),
    h0, h1, fun i => ?_⟩
  rw [← hsrc]
  exact hs i

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
