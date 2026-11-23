import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts)

theorem BdDivides.proof (hdiv : CoordDivDivisible.Statement) : BdDivides.Statement := by
  intro X _ D A R j k
  set Ω : Set (Fin D → ℂ) := (R.ψ j).target ∩ (R.ψ j).symm ⁻¹' (bdDom R j ∩ bdDom R k) with hΩdef
  have hΩ : IsOpen Ω :=
    (R.ψ j).isOpen_inter_preimage_symm ((isOpen_bdDom R j).inter (isOpen_bdDom R k))
  set F : (Fin D → ℂ) → ℂ := fun z => ∏ i ∈ R.S k, R.ψ k ((R.ψ j).symm z) i with hFdef
  have hF : AnalyticOnNhd ℂ F Ω := by
    intro z hz
    have ht : AnalyticAt ℂ (R.ψ k ∘ (R.ψ j).symm) z :=
      ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.compat_trans A (R.compat j) (R.compat k) hz.1 hz.2.2.1
    exact Finset.analyticAt_fun_prod (f := fun i z => R.ψ k ((R.ψ j).symm z) i) _
      fun i _ => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt _ |>.comp ht
  have hvan : ∀ z ∈ Ω, z ∈ coordDiv (R.S j) → F z = 0 := by
    intro z hz hzS
    obtain ⟨hzt, ⟨_, hzW⟩, ⟨hyk, hykW⟩⟩ := hz
    have hjz : R.ψ j ((R.ψ j).symm z) = z := (R.ψ j).right_inv hzt
    rw [Set.mem_preimage, hjz] at hzW
    have hnot : (R.ψ j).symm z ∉ R.Yo := fun h => ((R.mem_Yo_iff j z hzW).1 h) hzS
    have hk : R.ψ k ((R.ψ j).symm z) ∈ coordDiv (R.S k) := by
      by_contra hc
      apply hnot
      have := (R.mem_Yo_iff k _ hykW).2 hc
      rwa [(R.ψ k).left_inv hyk] at this
    obtain ⟨i, hi, h0⟩ := hk
    exact Finset.prod_eq_zero hi h0
  obtain ⟨G, hG, hFG⟩ := hdiv D Ω F (R.S j) hΩ hF hvan
  have hmem : ∀ y ∈ bdDom R j ∩ bdDom R k, R.ψ j y ∈ Ω := fun y hy =>
    ⟨(R.ψ j).map_source hy.1.1, by
      show (R.ψ j).symm (R.ψ j y) ∈ bdDom R j ∩ bdDom R k
      rw [(R.ψ j).left_inv hy.1.1]; exact hy⟩
  refine ⟨fun y => G (R.ψ j y), ?_, ?_, ?_⟩
  · intro m w hw
    have hx : (A.chart m).symm w ∈ bdDom R j ∩ bdDom R k := hw.2
    have hc : AnalyticAt ℂ (R.ψ j ∘ (A.chart m).symm) w := ((R.compat j) m).1 w ⟨hw.1, hx.1.1⟩
    exact (hG _ (hmem _ hx)).comp (f := R.ψ j ∘ (A.chart m).symm) hc
  · exact hG.continuousOn.comp ((R.ψ j).continuousOn.mono fun y hy => hy.1.1) hmem
  · intro y hy
    have h := hFG _ (hmem y hy)
    simp only [hFdef, (R.ψ j).left_inv hy.1.1] at h
    simp only [bdEq]
    rw [h, mul_comm]

end GroundTheory.Heights₂.Heights.AnalyticLimit
