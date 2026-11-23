import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.RealBracketHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCR
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoordCovolOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXKL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NofibOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ReImESymmAdd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNBoxOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PjFrameRow
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibFibC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRc

namespace Formalism.L2.SG.Closed

open Formalism.L2.SG.Pf.NcReal.JX in
theorem CovolRef_holds (hNL : NOfibLat) (hRB : CovB.RowBlockCovol) : CovolRef :=
  covolRef_of_steps (coordCovol_of kapLaw_holds (nofib_of hNL) (CovB.blockCovol_of hRB)) (refNBox_of Formalism.L2.SG.Pf.NcReal.JX.FR.frameRow_holds)

open Formalism.L2.SG.Pf.NcReal.JX in
variable [Fact PI.AprimeInfW.GaugeVolUD] [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem RealBracket_of_leaves (hNL : NOfibLat) (hRB : CovB.RowBlockCovol) :
    Formalism.L2.SG.Pf.NcReal.RealBracket :=
  RealBracket_holds (CovolRef_holds hNL hRB)

open Formalism.L2.SG.Pf.NcReal.JX in
theorem CovolRef_of_rowBlock (hRB : CovB.RowBlockCovol) : CovolRef :=
  covolRef_of_steps (coordCovol_of kapLaw_holds NOf.nofib_holds (CovB.blockCovol_of hRB))
    (refNBox_of Formalism.L2.SG.Pf.NcReal.JX.FR.frameRow_holds)

open Formalism.L2.SG.Pf.NcReal.JX in
variable [Fact PI.AprimeInfW.GaugeVolUD] [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem RealBracket_of_rowBlock (hRB : CovB.RowBlockCovol) : Formalism.L2.SG.Pf.NcReal.RealBracket :=
  RealBracket_holds (CovolRef_of_rowBlock hRB)

open Formalism.L2.SG.Pf.NcReal.JX in
theorem CovolRef_outright : CovolRef :=
  covolRef_of_steps (coordCovol_of kapLaw_holds NOf.nofib_holds Formalism.L2.SG.Pf.NcReal.JX.CovB.blockCovol_holds)
    (refNBox_of Formalism.L2.SG.Pf.NcReal.JX.FR.frameRow_holds)

variable [Fact PI.AprimeInfW.GaugeVolUD] [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem RealBracket_outright : Formalism.L2.SG.Pf.NcReal.RealBracket := RealBracket_holds CovolRef_outright

end Formalism.L2.SG.Closed
