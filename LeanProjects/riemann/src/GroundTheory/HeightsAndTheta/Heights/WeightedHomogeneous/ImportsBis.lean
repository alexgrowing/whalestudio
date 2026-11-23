import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsChartFormsIffIsFormSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

theorem ChartCrossRatio.equiv :
    GroundTheory.Heights₂.Heights.ChartCrossRatio.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartCrossRatio.Statement := by
  constructor
  · intro h ι _ _ n P D G c c' j
    exact h ι n P (AddBlockData.toObjects D) G.d G.g G.isFormSystem c c' j
  · intro h ι _ _ n P D d g hg c c' j
    exact h ι n P (AddBlockData.ofObjects D) (ChartForms.ofFormSystem hg) c c' j

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
