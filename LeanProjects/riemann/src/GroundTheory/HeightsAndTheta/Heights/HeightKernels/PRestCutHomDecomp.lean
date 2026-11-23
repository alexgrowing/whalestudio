import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem RestCutHomDecomp.proof : RestCutHomDecomp.Statement := by
  intro f N F Q d hF hFh hNd
  unfold RestTerms.IsPowerSumDecomposition at hF ⊢
  have h := congrArg (homogeneousComponent d) hF
  rw [homogeneousComponent_eq_self hFh] at h
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hlN : l ≤ N := (Finset.mem_Icc.mp hl).2
  have hp : (RestTerms.blockPowerSum f N l τ).IsHomogeneous l := by
    unfold RestTerms.blockPowerSum
    exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _
  rw [KRest.homogeneousComponent_mul_left hp, if_pos (hlN.trans hNd)]

end GroundTheory.Heights₂.Heights
