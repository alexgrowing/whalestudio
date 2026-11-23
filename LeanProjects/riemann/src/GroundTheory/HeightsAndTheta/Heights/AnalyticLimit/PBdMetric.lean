import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

noncomputable section

theorem BdMetric.proof (hCC : ChartCont.Statement) (hT : BdTransition.Statement)
    (hC : BdCocycle.Statement) (hL : LogNormHolo.Statement) (hW : BdWeight.Statement) :
    BdMetric.Statement := by
  intro X _ _ _ D A R
  choose g hgH hg using fun j k => hT D A R j k
  have hO : ∀ j k, IsOpen (bdDom R j ∩ bdDom R k) := fun j k =>
    (isOpen_bdDom R j).inter (isOpen_bdDom R k)
  have hgC : ∀ j k, ContinuousOn (g j k) (bdDom R j ∩ bdDom R k) := fun j k =>
    (hCC D A _ (hO j k)).2 _ (hgH j k)
  have hcoc := hC D A R g hgC fun j k y hy => (hg j k y hy).2
  obtain ⟨w, hwS, hwP, hwE⟩ := hW D A R g hgH (fun j k y hy => (hg j k y hy).1) hcoc

  have hd : ∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k,
      Real.log (w j y) / 2 = Real.log ‖g j k y‖ + Real.log (w k y) / 2 := by
    intro j k y hy
    have hg0 : ‖g j k y‖ ≠ 0 := norm_ne_zero_iff.mpr (hg j k y hy).1
    rw [hwE j k y hy, Real.log_mul (pow_ne_zero 2 hg0) (hwP k y hy.2).ne', Real.log_pow]
    push_cast
    ring
  refine ⟨fun j y => Real.log (w j y) / 2, fun j i => ?_, fun j k y hy => ?_, fun j k y hy => ?_⟩
  · exact ((hwS j i).log fun z hz => (hwP j _ hz.2).ne').div_const 2
  · obtain ⟨V, hV, hyV, hVW, G, hG, hGe⟩ :=
      hL D A _ (g j k) (hO j k) (hgH j k) (fun z hz => (hg j k z hz).1) y hy
    refine ⟨V, hV, hyV, G, hG, fun z hz => ?_⟩
    show Real.log (w j z) / 2 - Real.log (w k z) / 2 = (G z).re
    rw [hd j k z hz.2, ← hGe z hz.1]
    ring
  · have hgp : 0 < ‖g j k y‖ := norm_pos_iff.mpr (hg j k y hy).1
    simp only
    rw [hd j k y hy, (hg j k y hy).2, norm_mul, neg_add, Real.exp_add, Real.exp_neg (Real.log _),
      Real.exp_log hgp]
    field_simp

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
