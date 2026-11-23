import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RenameBaseHomogeneousComponent
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsFormDivOfMemChartRing
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsAlgebraicAdjoin
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ProdExp
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SpanSecsMemLocInSelf
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.FoldTensorToSubSystem
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCombCyclic
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCombContract
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHTheoremSFree
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeEmbed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeDecomp
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeIndep
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeBadFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechSES
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechDSq
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechDDeg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHTheoremS
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHPrimeFilt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperComponentMulX
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PEulerVarX
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsPolyBackDiffPow
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotPartEqGradedPiece
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsPowSmulEqZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisBis
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsFormOfMemChartRingOver
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellMeetsPt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsPowOfMemCellSec
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SetCApplyNotMem
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellDMulLeft
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiHomogRename
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRowLocCoverX
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellMeetsBaseCell
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SgnSingleton
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDoubleCechX
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LineBundleTwistVanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechDMemLocPart
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.FinrankSectionsOverEqH0
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.DegreeOneCellEqChartUpdate
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AltSumEqOfEventually
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XMemMIdealOverIff
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocAtRatio
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XBaseMemMIdealOverGraph
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemMIdealOverIff
import Development.WeilBound.CoreStatements.HodgeTatePoints.Imports

namespace PositivityTheory.HtPt.Ktw

theorem a0 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CurveComap.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CurveComap.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SectionRatio.full
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RatioDim.full

theorem a6 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.TensorRealises.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.TensorRealises.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelGenerated.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SpanSecs.proof

theorem a7 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.TensorRealise.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.TensorRealise.proof a6

theorem a8 :
    GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic.proof
    GroundTheory.Heights₂.Heights.Kleiman.KHCombContract.full

theorem a9 :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSFreeStatement :=
  GroundTheory.Heights₂.Heights.Kleiman.KHTheoremSFree.proof
    GroundTheory.Heights₂.Heights.Kleiman.KHFreeEmbed.full
    GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp.full
    GroundTheory.Heights₂.Heights.Kleiman.KHFreeIndep.full
    GroundTheory.Heights₂.Heights.Kleiman.KHCombContract.full a8
    GroundTheory.Heights₂.Heights.Kleiman.KHFreeBadFinite.full

theorem a10 :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechSESStatement :=
  GroundTheory.Heights₂.Heights.Kleiman.KHCechSES.proof
    GroundTheory.Heights₂.Heights.Kleiman.KHCechDSq.full
    GroundTheory.Heights₂.Heights.Kleiman.KHCechDDeg.full

theorem a11 :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement :=
  GroundTheory.Heights₂.Heights.Kleiman.KHTheoremS.proof a9 a10
    GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt.full

theorem a12 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerPoly.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerPoly.proof a11
    GroundTheory.Heights₂.Heights.Swarm.EulerVar.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.PolyOfDiffsExact.full

theorem a13 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.MultiSerre.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.MultiSerre.proof a11
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SectionMapInj.full

theorem a14 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelRowExact.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelRowExact.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSub.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellZeroConst.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellContract.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocGlue.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowChartAct.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowLocCover.closed

theorem a15 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCechRefine.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCechRefine.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CechContract.proof a14
    GroundTheory.Heights₂.Heights.Swarm.DoubleCech.proof

theorem a16 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RayVanish.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RayVanish.proof_of_ties
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval.proof a15

theorem a17 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SectionsPoly.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SectionsPoly.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.HZeroRowPlaceData.full a12 a13 a16

theorem a18 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NumModel.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NumModel.proof a7 a17
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelDim.proof

theorem a19 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.DegEq.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.DegEq.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.GraphRestrict.full a5 a18

theorem a20 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefEq.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefEq.proof a0
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CurveLift.full a19

end PositivityTheory.HtPt.Ktw
