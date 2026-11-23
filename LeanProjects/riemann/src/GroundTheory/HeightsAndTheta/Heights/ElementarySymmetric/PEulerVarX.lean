import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechHcEqCoh
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CohMkEqZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechDSq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem EulerVar.proof : GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerVar.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerVar.proof
    GroundTheory.Heights₂.Heights.Kleiman.KHCechDSq.full
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES.full

end GroundTheory.Heights₂.Heights.Swarm
