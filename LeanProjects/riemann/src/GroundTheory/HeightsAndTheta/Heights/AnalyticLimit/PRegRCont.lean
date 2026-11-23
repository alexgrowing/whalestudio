import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open Filter Topology

theorem RegRCont.proof : RegRCont.Statement := by
  intro X _ D A R y hy
  set j := bdIdx R y
  have hyU : y ∈ bdDom R j := mem_bdDom_bdIdx R y
  let g : (Fin D → ℂ) → ℝ := fun z =>
    Real.exp 1 + R.f j z - ∑ i ∈ R.S j, Real.log (‖z i‖ ^ 2)
  have key : ∀ y' ∈ bdDom R j ∩ R.Yo,
      R.ψ j y' ∉ coordDiv (R.S j) ∧ R.r y' = g (R.ψ j y') := by
    rintro y' ⟨⟨hs, hW⟩, hY⟩
    have hinv : (R.ψ j).symm (R.ψ j y') = y' := (R.ψ j).left_inv hs
    have hnot : R.ψ j y' ∉ coordDiv (R.S j) :=
      (R.mem_Yo_iff j _ hW).1 (by rw [hinv]; exact hY)
    refine ⟨hnot, ?_⟩
    have h := R.r_chart j (R.ψ j y') ⟨hW, hnot⟩
    rw [hinv] at h
    exact h
  have hg : ContinuousAt g (R.ψ j y) := by
    have hW : R.ψ j y ∈ R.W j := hyU.2
    have hnd := (key y ⟨hyU, hy⟩).1
    have hf : ContinuousAt (R.f j) (R.ψ j y) :=
      (R.f_cont j).continuousAt ((R.isOpen_kappaOpenNeighbourhood j).mem_nhds hW)
    refine (continuousAt_const.add hf).sub ?_
    refine tendsto_finsetSum (R.S j) fun i hi => ?_
    have hzi : R.ψ j y i ≠ 0 := fun h0 => hnd ⟨i, hi, h0⟩
    have hc : ContinuousAt (fun z : Fin D → ℂ => ‖z i‖ ^ 2) (R.ψ j y) :=
      ((continuous_apply i).norm.pow 2).continuousAt
    exact hc.log (pow_ne_zero 2 (norm_ne_zero_iff.2 hzi))
  have hO : IsOpen (bdDom R j ∩ R.Yo) := (isOpen_bdDom R j).inter R.isOpen_Yo
  have heq : g ∘ R.ψ j =ᶠ[𝓝 y] R.r :=
    Filter.eventually_of_mem (hO.mem_nhds ⟨hyU, hy⟩) fun y' h => ((key y' h).2).symm
  exact ((hg.comp ((R.ψ j).continuousAt hyU.1)).congr heq).continuousWithinAt

end GroundTheory.Heights₂.Heights.AnalyticLimit
