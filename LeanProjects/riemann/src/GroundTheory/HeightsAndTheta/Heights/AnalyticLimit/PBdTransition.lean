import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem BdTransition.proof (hDense : RegYoDense.Statement) (hEq : BdEqHolo.Statement)
    (hDiv : BdDivides.Statement) : BdTransition.Statement := by
  intro X _ D A R j k
  obtain ⟨u, hu, huc, hue⟩ := hDiv D A R k j
  obtain ⟨v, -, hvc, hve⟩ := hDiv D A R j k
  have hO : bdDom R k ∩ bdDom R j = bdDom R j ∩ bdDom R k := Set.inter_comm _ _
  rw [hO] at hu huc hue
  set O := bdDom R j ∩ bdDom R k with hOdef
  have hOopen : IsOpen O := (isOpen_bdDom R j).inter (isOpen_bdDom R k)

  have hYo : Set.EqOn (fun y => u y * v y) (fun _ => (1 : ℂ)) (O ∩ R.Yo) := by
    intro y ⟨hyO, hyY⟩
    have hne : bdEq R j y ≠ 0 := fun h0 => ((hEq D A R j).2 y hyO.1).1 h0 hyY
    have h1 : bdEq R j y = (u y * v y) * bdEq R j y := by
      rw [mul_assoc, ← hve y hyO, ← hue y hyO]
    have h2 : (u y * v y) * bdEq R j y = 1 * bdEq R j y := by rw [← h1, one_mul]
    exact mul_right_cancel₀ hne h2

  have hall : Set.EqOn (fun y => u y * v y) (fun _ => (1 : ℂ)) O :=
    hYo.of_subset_closure (huc.mul hvc) continuousOn_const Set.inter_subset_left
      ((hDense D A R).open_subset_closure_inter hOopen)
  refine ⟨u, hu, fun y hy => ⟨fun h0 => ?_, hue y hy⟩⟩
  have := hall hy
  simp only [h0, zero_mul] at this
  exact zero_ne_one this

end GroundTheory.Heights₂.Heights.AnalyticLimit
