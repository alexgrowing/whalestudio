import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StMIntegrableOfDensLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot locDens MIntegrable)

theorem MIntegrableOfDensLe.proof : MIntegrableOfDensLe.Statement := by
  intro D X _ A V Φ Ψ hV hΦc hΨc hle g hg hΨ j K hK hKc
  set e := A.chart j
  set dΦ := locDens A Φ j
  set dΨ := locDens A Ψ j
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' V) := e.isOpen_inter_preimage_symm hV
  set W := (e.target ∩ e.symm ⁻¹' V) ∩ dΨ ⁻¹' Set.Ioi 0 with hWdef
  have hW : IsOpen W := (hΨc j).isOpen_inter_preimage hO isOpen_Ioi
  set q : (Fin D → ℂ) → ℝ := W.indicator (fun y => dΦ y / dΨ y) with hqdef
  have hqc : ContinuousOn (fun y => dΦ y / dΨ y) W :=
    ((hΦc j).mono Set.inter_subset_left).div ((hΨc j).mono Set.inter_subset_left)
      (fun y hy => (ne_of_gt hy.2))
  have hqm : AEStronglyMeasurable q (volume.restrict K) :=
    ((aestronglyMeasurable_indicator_iff hW.measurableSet).2
      (hqc.aestronglyMeasurable hW.measurableSet)).restrict
  have hqb : ∀ y, ‖q y‖ ≤ 1 := by
    intro y
    by_cases hy : y ∈ W
    · have hpos : 0 < dΨ y := hy.2
      obtain ⟨h0, h1⟩ := hle j y hy.1.1 hy.1.2
      rw [hqdef, Set.indicator_of_mem hy, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg h0 hpos.le)]
      exact (div_le_one hpos).2 h1
    · rw [hqdef, Set.indicator_of_notMem hy, norm_zero]
      exact zero_le_one
  have hint : IntegrableOn (fun y => (g (e.symm y) * dΨ y) * q y) K :=
    Integrable.mul_bdd (hΨ j K hK hKc) hqm (Filter.Eventually.of_forall hqb)
  refine hint.congr_fun ?_ hKc.measurableSet
  intro y hy
  have hyt : y ∈ e.target := hK hy
  simp only
  by_cases hyV : e.symm y ∈ V
  · obtain ⟨h0, h1⟩ := hle j y hyt hyV
    by_cases hpos : 0 < dΨ y
    · have hyW : y ∈ W := ⟨⟨hyt, hyV⟩, hpos⟩
      rw [hqdef, Set.indicator_of_mem hyW]
      field_simp
    · have hyW : y ∉ W := fun h => hpos h.2
      have hz : dΦ y = 0 := le_antisymm (h1.trans (not_lt.1 hpos)) h0
      rw [hqdef, Set.indicator_of_notMem hyW, hz]
      ring
  · rw [hg _ hyV]
    ring

end GroundTheory.Heights₂.Heights.AnalyticLimit
