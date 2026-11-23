import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartIntegral
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisor
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsIntegralProjIndep
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsIntegralSegreChartProj
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSemiPosMassFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartProjFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartZeroSet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartSheetCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMassFiniteDirect
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimOfChowForm
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealDim
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealPrime
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncidenceGeneric
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PFGNullstellensatz
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PGenericLinearTrdeg
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.UniformIntegrabilityProportionalityHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.TargetsProjGenericRank
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosDensIntegrable
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.SegreChart

theorem Chart.incIdealDim : GroundTheory.Heights₂.Heights.IncIdealDim.Statement :=
  GroundTheory.Heights₂.Heights.IncIdealDim.proof
    (GroundTheory.Heights₂.Heights.IncidenceGeneric.proof GroundTheory.Heights₂.Heights.FGNullstellensatz.proof)
    GroundTheory.Heights₂.Heights.GenericLinearTrdeg.proof GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof

theorem Chart.incIdealPrime : GroundTheory.Heights₂.Heights.IncIdealPrime.Statement :=
  GroundTheory.Heights₂.Heights.IncIdealPrime.proof
    (GroundTheory.Heights₂.Heights.IncidenceGeneric.proof GroundTheory.Heights₂.Heights.FGNullstellensatz.proof)

theorem Chart.coneDimOfChowForm : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
  GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof Chart.incIdealDim Chart.incIdealPrime

theorem Chart.GoodChartDim : GroundTheory.Heights₂.Heights.GoodChartDim.Statement :=
  @GroundTheory.Heights₂.Heights.GoodChartDim.proof GroundTheory.Heights₂.Heights.ConeVanishingHomog.proof GroundTheory.Heights₂.Heights.ConeSliceIdeal.proof GroundTheory.Heights₂.Heights.ChartDehomogPrime.proof

theorem Chart.GoodChartModel : GroundTheory.Heights₂.Heights.GoodChartModel.Statement :=
  @GroundTheory.Heights₂.Heights.GoodChartModel.proof GroundTheory.Heights₂.Heights.GoodChartZeroSet.proof Chart.GoodChartDim

theorem Chart.PtsGenericCount : GroundTheory.Heights₂.Heights.PtsGenericCount.Statement :=
  @GroundTheory.Heights₂.Heights.PtsGenericCount.proof Chart.GoodChartModel GroundTheory.Heights₂.Heights.ComponentsGenericCount.proof GroundTheory.Heights₂.Heights.SheetLift.proof

theorem Chart.PtsSheetSimpleNull : GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.proof Chart.PtsGenericCount

theorem Chart.PtsSheetOnlyNull : GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.proof GroundTheory.Heights₂.Heights.CriticalFibreInfinite.proof

theorem Chart.PtsPosPartProjIndep : GroundTheory.Heights₂.Heights.PtsPosPartProjIndep.Statement :=
  @GroundTheory.Heights₂.Heights.PtsPosPartProjIndep.proof Chart.PtsSheetSimpleNull Chart.PtsSheetOnlyNull GroundTheory.Heights₂.Heights.PtsPosPartLocal.proof GroundTheory.Heights₂.Heights.PtsPosDensMeasurable.proof

theorem Chart.PtsSegreChartFibreSum : GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum.proof GroundTheory.Heights₂.Heights.SegreChartZeroSet.proof GroundTheory.Heights₂.Heights.SegreChartProjFinite.proof

theorem Chart.DiscriminantSheetCover : GroundTheory.Heights₂.Heights.DiscriminantSheetCover.Statement :=
  @GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ComplexSets.DiscriminantCover

theorem Chart.ConeSliceSheetParam : GroundTheory.Heights₂.Heights.ConeSliceSheetParam.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSliceSheetParam.proof Chart.DiscriminantSheetCover

theorem Chart.AreaFormulaInjSet : GroundTheory.Heights₂.Heights.AreaFormulaInjSet.Statement :=
  @GroundTheory.Heights₂.Heights.AreaFormulaInjSet.proof GroundTheory.Heights₂.Heights.AreaFormulaLocal.proof

theorem Chart.AreaFormulaInj : GroundTheory.Heights₂.Heights.AreaFormulaInj.Statement :=
  @GroundTheory.Heights₂.Heights.AreaFormulaInj.proof Chart.AreaFormulaInjSet

theorem Chart.ConeMapAreaOne : GroundTheory.Heights₂.Heights.ConeMapAreaOne.Statement :=
  @GroundTheory.Heights₂.Heights.ConeMapAreaOne.proof Chart.AreaFormulaInj

theorem Chart.ConeMapArea : GroundTheory.Heights₂.Heights.ConeMapArea.Statement :=
  @GroundTheory.Heights₂.Heights.ConeMapArea.proof Chart.ConeMapAreaOne

theorem Chart.ConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.proof Chart.ConeSliceSheetParam Chart.ConeMapArea

theorem Chart.SliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement :=
  @GroundTheory.Heights₂.Heights.SliceMassFinite.proof' Chart.ConeSheetGramLintegral GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.MassFinite Chart.coneDimOfChowForm

theorem Chart.SegreChartAbsIntegrable : GroundTheory.Heights₂.Heights.SegreChartAbsIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.SegreChartAbsIntegrable.proof Chart.SliceMassFinite GroundTheory.Heights₂.Heights.SegreChartSheetCompare.proof

theorem Chart.PtsSemiPosMassFinite : GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.proof Chart.PtsPosPartProjIndep Chart.PtsSegreChartFibreSum Chart.SegreChartAbsIntegrable

theorem Chart.PtsPosDensIntegrable : GroundTheory.Heights₂.Heights.PtsPosDensIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.PtsPosDensIntegrable.proof Chart.PtsSemiPosMassFinite

theorem Chart.PtsIntegralProjIndep : GroundTheory.Heights₂.Heights.PtsIntegralProjIndep.Statement :=
  @GroundTheory.Heights₂.Heights.PtsIntegralProjIndep.proof Chart.PtsPosDensIntegrable Chart.PtsPosPartProjIndep

theorem Chart.PtsIntegralSegreChartProj : GroundTheory.Heights₂.Heights.PtsIntegralSegreChartProj.Statement :=
  @GroundTheory.Heights₂.Heights.PtsIntegralSegreChartProj.proof GroundTheory.Heights₂.Heights.SegreChartProjFinite.proof GroundTheory.Heights₂.Heights.SegreChartZeroSet.proof Chart.SegreChartAbsIntegrable Chart.PtsSegreChartFibreSum

theorem Chart.SegreChartIntegral : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement :=
  @GroundTheory.Heights₂.Heights.SegreChartIntegral.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SegreCoordGoodProj Chart.PtsIntegralProjIndep Chart.PtsIntegralSegreChartProj

end GlobalTheory.CompanionTheory.Ar.SegreChart
