import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.AddBlockEquivSymmChartRingMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

theorem ChartPrimality.equiv :
    GroundTheory.Heights₂.Heights.ChartPrimality.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartPrimality.Statement := by
  constructor
  · intro hA ι _ _ n P D
    obtain ⟨Q, hQ⟩ := hA ι n P (AddBlockEq.split_model_to_place_model D)
    exact ⟨Q, hQ.trans (AddBlockEq.addBlockEquiv_symm_extIdeal D)⟩
  · intro hB ι _ _ n P D
    obtain ⟨Q, hQ⟩ := hB ι n P (AddBlockEq.toIndefiniteRowSideFullHecke D)
    exact ⟨Q, hQ.trans (AddBlockEq.addBlockEquiv_extIdeal D)⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
