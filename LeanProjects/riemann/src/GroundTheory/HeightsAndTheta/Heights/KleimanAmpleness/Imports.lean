import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellResMemLocPart
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechConstVanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsOfMemChartRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem CechPointVanish.full : CechPointVanish.Statement :=
  CechPointVanish.proof CechConstVanish.full CechPointEval.full

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
