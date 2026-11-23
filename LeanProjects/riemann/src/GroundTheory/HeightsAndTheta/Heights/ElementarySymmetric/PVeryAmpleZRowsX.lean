import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZRows
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechPartition
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PZChartSmul
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PZChartLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem VeryAmpleZRows.proof_closed : VeryAmpleZRows.Statement.{u, v, w} :=
  VeryAmpleZRows.proof CechPartition.proof ZChartSmul.proof (ZChartLocal.proof ZChartSmul.proof)

end GroundTheory.Heights₂.Heights.Kleiman
