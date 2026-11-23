import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchFillDimension
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchGermDimOne
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCentredDiscCoverCurve
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveMinimalPrimeQuotient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDominantFibreBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicFibreInfinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOffZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimComponentBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaceOnComponent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PReducedNormalisationPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegConeLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetImageArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarIntAdd
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarMassNearSmall
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PZeroDimIsolated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.HausdorffMeasureEuclideanSpaceEqVolume
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.branchOffHypersurface_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.LogIntegrable : GroundTheory.Heights₂.Heights.LogIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.LogIntegrable.proof GroundTheory.Heights₂.Heights.SheetSumMeasurable.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompare GroundTheory.Heights₂.Heights.VarSlabMeasure.full GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.MassFinite

theorem GroundTheory.Heights₂.Heights.AutoClose.VarIntAdd : GroundTheory.Heights₂.Heights.VarIntAdd.Statement :=
  @GroundTheory.Heights₂.Heights.VarIntAdd.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact

theorem GroundTheory.Heights₂.Heights.AutoClose.RegConeLimit : GroundTheory.Heights₂.Heights.RegConeLimit.Statement :=
  @GroundTheory.Heights₂.Heights.RegConeLimit.proof GroundTheory.Heights₂.Heights.ConeBallFinite.full GroundTheory.Heights₂.Heights.ConeFsLogIntegrable.full GroundTheory.Heights₂.Heights.ConeHyperplaneNull.full

theorem GroundTheory.Heights₂.Heights.AutoClose.SheetAreaCompare : GroundTheory.Heights₂.Heights.SheetAreaCompare.Statement :=
  @GroundTheory.Heights₂.Heights.SheetAreaCompare.of_open GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SheetImageAreaSet

theorem GroundTheory.Heights₂.Heights.AutoClose.BranchGermDimOne : GroundTheory.Heights₂.Heights.BranchGermDimOne.Statement :=
  @GroundTheory.Heights₂.Heights.BranchGermDimOne.proof GroundTheory.Heights₂.Heights.LocalDimComponentBound.proof GroundTheory.Heights₂.Heights.ZeroDimIsolated.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.full

theorem GroundTheory.Heights₂.Heights.AutoClose.LelongRegularise : GroundTheory.Heights₂.Heights.LelongRegularise.Statement :=
  @GroundTheory.Heights₂.Heights.LelongRegularise.of_open GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SheetImageAreaSet

theorem GroundTheory.Heights₂.Heights.AutoClose.DominantFibreBound : GroundTheory.Heights₂.Heights.DominantFibreBound.Statement :=
  @GroundTheory.Heights₂.Heights.DominantFibreBound.proof GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.full

theorem GroundTheory.Heights₂.Heights.AutoClose.SheetImageArea : GroundTheory.Heights₂.Heights.SheetImageArea.Statement :=
  @GroundTheory.Heights₂.Heights.SheetImageArea.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SheetImageAreaSet

theorem GroundTheory.Heights₂.Heights.AutoClose.branchFillDimension_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.centredDiscCoverCurve_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredDiscCoverCurve.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredDiscCoverCurve.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PuncturedCoverCycles.full

theorem GroundTheory.Heights₂.Heights.AutoClose.PlaceOnComponent : GroundTheory.Heights₂.Heights.PlaceOnComponent.Statement :=
  @GroundTheory.Heights₂.Heights.PlaceOnComponent.proof GroundTheory.Heights₂.Heights.ReducedNormalisationPlace.proof GroundTheory.Heights₂.Heights.CurveMinimalPrimeQuotient.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.DiscriminantSheetCover : GroundTheory.Heights₂.Heights.DiscriminantSheetCover.Statement :=
  @GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ComplexSets.DiscriminantCover

theorem GroundTheory.Heights₂.Heights.AutoClose.LelongLimitOffZero : GroundTheory.Heights₂.Heights.LelongLimitOffZero.Statement :=
  @GroundTheory.Heights₂.Heights.LelongLimitOffZero.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact

theorem GroundTheory.Heights₂.Heights.AutoClose.areaGraph_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AreaGraph.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AreaGraph.rowPoisson_half_implies_one GroundTheory.Heights₂.Heights.AreaGraph.full

theorem GroundTheory.Heights₂.Heights.AutoClose.VarMassNearSmall : GroundTheory.Heights₂.Heights.VarMassNearSmall.Statement :=
  @GroundTheory.Heights₂.Heights.VarMassNearSmall.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact
