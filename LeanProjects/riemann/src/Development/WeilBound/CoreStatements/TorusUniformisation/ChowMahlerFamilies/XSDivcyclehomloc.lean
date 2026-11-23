import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleHomLoc
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingIsLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingNoetherian
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingDimLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingLocal

namespace PositivityTheory.Xgn.A_s_divcyclehomloc

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem homLocRingLocal : HomLocRingLocal.Statement.{0} :=
  HomLocRingLocal.proof (HomLocRingIsLocal.proof HomLocRingMem.proof)
    (HomLocRingNoetherian.proof HomLocRingMem.proof)
    (HomLocRingDimLe.proof HomLocRingMem.proof (HomLocRingIsLocal.proof HomLocRingMem.proof))

end PositivityTheory.Xgn.A_s_divcyclehomloc

theorem PositivityTheory.Xgn.t_s_divcyclehomloc : GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.Statement.{0} :=
  GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.proof PositivityTheory.Xgn.A_s_divcyclehomloc.homLocRingLocal
