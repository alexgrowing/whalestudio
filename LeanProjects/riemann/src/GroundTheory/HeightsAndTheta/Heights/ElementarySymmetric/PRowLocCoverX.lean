import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AevalNeZeroOfMemCellMon
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PChartSecGen
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PChartSecMul
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsFormOfMemChartRingOver
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiHomogRename
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem RowLocCover.closed : RowLocCover.Statement :=
  RowLocCover.proof ChartSecGen.full (ChartSecMul.proof BundleOfDeg.full) RowSub.proof
    RowChartAct.proof

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
