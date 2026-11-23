import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.AddBlockEquivSymmChartRingMap
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsChartFormsIffIsFormSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

theorem SectionCycle.equiv :
    GroundTheory.Heights₂.Heights.SectionCycle.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.SectionCycle.Statement := by
  constructor
  · intro hA ι _ _ n P D G c j hg W
    have e : (AddBlockEq.split_model_to_place_model D).extIdeal = D.ext := AddBlockEq.addBlockEquiv_symm_extIdeal D
    have h := hA ι n P (AddBlockEq.split_model_to_place_model D) G.d G.g G.isFormSystem c j
      (by rw [e]; exact hg) W
    rw [e] at h
    exact h
  · intro hB ι _ _ n P D d g hfs c j hg W
    have e : (AddBlockEq.toIndefiniteRowSideFullHecke D).ext = D.extIdeal := AddBlockEq.addBlockEquiv_extIdeal D
    have h := hB ι n P (AddBlockEq.toIndefiniteRowSideFullHecke D) (ChartForms.ofFormSystem hfs) c j
      (by rw [e]; exact hg) W
    rw [e] at h
    exact h

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
