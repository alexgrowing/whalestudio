import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PNumberFieldBoxCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLatticeImageZLattice
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCovolumeRelIndex
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PEmbeddingSumPlaces
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PMixedBoxCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLatticeCountVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

theorem NumberFieldBoxCount.proof_closed : NumberFieldBoxCount.Statement :=
  NumberFieldBoxCount.proof LatticeImageZLattice.proof CovolumeRelIndex.proof EmbeddingSumPlaces.proof
    (MixedBoxCount.proof LatticeCountVolume.proof)

end GroundTheory.Heights₂.Heights.Targets
