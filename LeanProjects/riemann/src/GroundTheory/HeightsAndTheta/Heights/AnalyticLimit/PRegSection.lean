import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection logNormSec)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem RegSection.proof (hDense : RegYoDense.Statement) (hRC : RegRCont.Statement)
    (hMet : BdMetric.Statement) (hProps : BdSectionProps.Statement)
    (hNorm : BdNormCont.Statement) (hCmp : BdComparison.Statement) : RegSection.Statement := by
  intro X _ _ _ D A R
  obtain ⟨φ, hφ⟩ := hMet D A R
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y : X,
      ‖bdSec R y y‖ * Real.exp (-(bdPot R φ 0).φ y y) ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_univ.image (hNorm D A R φ hφ 0)).bddAbove
    exact ⟨M, fun y => hM ⟨y, Set.mem_univ _, rfl⟩⟩
  have hM1 : (0 : ℝ) < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set c := Real.log (max M 1) with hc
  have hφc : ∀ y : X, (bdPot R φ c).φ y y = (bdPot R φ 0).φ y y + c := fun y => by
    simp [bdPot]
  obtain ⟨hPot, hSec, hOpen⟩ := hProps D A R φ hφ c
  have hle : ∀ y : X, ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y) ≤ 1 := by
    intro y
    rw [hφc, neg_add, Real.exp_add, ← mul_assoc, Real.exp_neg c, hc, Real.exp_log hM1,
      mul_inv_le_iff₀ hM1, one_mul]
    exact (hM y).trans (le_max_left _ _)
  refine ⟨bdPot R φ c, bdSec R, hPot, hSec, hle, hOpen, hDense D A R, hRC D A R, ?_,
    hCmp D A R φ hφ c⟩
  have hne : ∀ y ∈ R.Yo, ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y) ≠ 0 := by
    intro y hy
    rw [← hOpen] at hy
    exact mul_ne_zero (norm_ne_zero_iff.2 hy) (Real.exp_pos _).ne'
  have hlog : ContinuousOn (fun y => logNormSec (bdPot R φ c) (bdSec R) y) R.Yo :=
    (hNorm D A R φ hφ c).continuousOn.log hne
  exact continuousOn_const.sub (continuousOn_const.mul hlog)

end GroundTheory.Heights₂.Heights.AnalyticLimit
