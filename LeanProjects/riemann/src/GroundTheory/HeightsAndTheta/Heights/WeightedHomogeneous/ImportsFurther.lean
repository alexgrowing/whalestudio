import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.FunFieldEquivMemChartRingIff
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.AddBlockEquivSymmChartRingMap
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsChartFormsIffIsFormSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open AddBlockEq

theorem ConePointsConverse.equiv :
    GroundTheory.Heights₂.Heights.ConePointsConverse.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ConePointsConverse.Statement := by
  constructor
  · intro hA ι _ _ n P D G z hz c hc
    have h := hA ι n P (split_model_to_place_model D) G.d G.g G.isFormSystem z hz c hc
    rw [addBlockEquiv_symm_conePoints] at h
    have e : (D.join z fun j ↦ evalCone z (G.g c j)) = (split_model_to_place_model D).joinPt z fun j ↦ evalCone z (G.g c j) := by
      funext o
      cases o <;> rfl
    rw [e]
    exact h
  · intro hB ι _ _ n P D d g hg z hz c hc
    have h := hB ι n P (toIndefiniteRowSideFullHecke D) (ChartForms.ofFormSystem hg) z hz c hc
    rw [extPoints_eq, ← addBlockEquiv_join]
    exact h

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
