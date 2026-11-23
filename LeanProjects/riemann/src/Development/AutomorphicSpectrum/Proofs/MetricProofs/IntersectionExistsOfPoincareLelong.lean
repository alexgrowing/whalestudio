import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsMultiHomogIdealMapRedMap
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIExists
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmISymm
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArIntMul
import GroundTheory.HeightsAndTheta.Heights.Intersections.PWellDefined
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSwapCycles
import GroundTheory.HeightsAndTheta.Heights.Intersections.PGeoNumCut
import GroundTheory.HeightsAndTheta.Heights.Intersections.DeEqZeroOfSemiPosOff
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDeSlotAdd
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDeLeSemiPos
import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsMeasurable
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAddFirst
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsRegLimit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Stokes
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsBilinear
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.IntNumCompPerm
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GeoNum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.NumbersDVRC3ResidualContractionComponent
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChart
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvdOfForallEmultiplicityLe
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartZeroSet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartProjFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartSheetCompare
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaLocal
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaInjSet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSegreChartFibreSum
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapAreaOne
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapArea
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaInj
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeSheetGramLintegral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMassFiniteDirect
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeSliceSheetParam
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosDensMeasurable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsIntegralSegreChartProj
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCriticalFibreInfinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosPartLocal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetOnlyNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PComponentsGenericCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSheetLift
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDehomogPrime
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsGenericCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSemiPosMassFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosDensIntegrable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeVanishingHomog
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetSimpleNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosPartProjIndep
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartZeroSet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartIntegral
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsIntegralProjIndep

namespace GlobalTheory.CompanionTheory.Ar.Pub

open GroundTheory.Heights₂.Heights

theorem Seg.GoodChartDim : GroundTheory.Heights₂.Heights.GoodChartDim.Statement :=
  @GroundTheory.Heights₂.Heights.GoodChartDim.proof GroundTheory.Heights₂.Heights.ConeVanishingHomog.proof GroundTheory.Heights₂.Heights.ConeSliceIdeal.proof GroundTheory.Heights₂.Heights.ChartDehomogPrime.proof

theorem Seg.GoodChartModel : GroundTheory.Heights₂.Heights.GoodChartModel.Statement :=
  @GroundTheory.Heights₂.Heights.GoodChartModel.proof GroundTheory.Heights₂.Heights.GoodChartZeroSet.proof Seg.GoodChartDim

theorem Seg.PtsGenericCount : GroundTheory.Heights₂.Heights.PtsGenericCount.Statement :=
  @GroundTheory.Heights₂.Heights.PtsGenericCount.proof Seg.GoodChartModel GroundTheory.Heights₂.Heights.ComponentsGenericCount.proof GroundTheory.Heights₂.Heights.SheetLift.proof

theorem Seg.PtsSheetSimpleNull : GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.proof Seg.PtsGenericCount

theorem Seg.PtsSheetOnlyNull : GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.proof GroundTheory.Heights₂.Heights.CriticalFibreInfinite.proof

theorem Seg.PtsPosPartProjIndep : GroundTheory.Heights₂.Heights.PtsPosPartProjIndep.Statement :=
  @GroundTheory.Heights₂.Heights.PtsPosPartProjIndep.proof Seg.PtsSheetSimpleNull Seg.PtsSheetOnlyNull GroundTheory.Heights₂.Heights.PtsPosPartLocal.proof GroundTheory.Heights₂.Heights.PtsPosDensMeasurable.proof

theorem Seg.PtsSegreChartFibreSum : GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum.proof GroundTheory.Heights₂.Heights.SegreChartZeroSet.proof GroundTheory.Heights₂.Heights.SegreChartProjFinite.proof

theorem Seg.DiscriminantSheetCover : GroundTheory.Heights₂.Heights.DiscriminantSheetCover.Statement :=
  @GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ComplexSets.DiscriminantCover

theorem Seg.ConeSliceSheetParam : GroundTheory.Heights₂.Heights.ConeSliceSheetParam.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSliceSheetParam.proof Seg.DiscriminantSheetCover

theorem Seg.AreaFormulaInjSet : GroundTheory.Heights₂.Heights.AreaFormulaInjSet.Statement :=
  @GroundTheory.Heights₂.Heights.AreaFormulaInjSet.proof GroundTheory.Heights₂.Heights.AreaFormulaLocal.proof

theorem Seg.AreaFormulaInj : GroundTheory.Heights₂.Heights.AreaFormulaInj.Statement :=
  @GroundTheory.Heights₂.Heights.AreaFormulaInj.proof Seg.AreaFormulaInjSet

theorem Seg.ConeMapAreaOne : GroundTheory.Heights₂.Heights.ConeMapAreaOne.Statement :=
  @GroundTheory.Heights₂.Heights.ConeMapAreaOne.proof Seg.AreaFormulaInj

theorem Seg.ConeMapArea : GroundTheory.Heights₂.Heights.ConeMapArea.Statement :=
  @GroundTheory.Heights₂.Heights.ConeMapArea.proof Seg.ConeMapAreaOne

theorem Seg.ConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.proof Seg.ConeSliceSheetParam Seg.ConeMapArea

theorem Seg.SliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement :=
  @GroundTheory.Heights₂.Heights.SliceMassFinite.proof' Seg.ConeSheetGramLintegral GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.MassFinite GlobalTheory.CompanionTheory.Ar.Short.ChowClosing.SectionPerfect.coneDimOfChowForm_full

theorem Seg.SegreChartAbsIntegrable : GroundTheory.Heights₂.Heights.SegreChartAbsIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.SegreChartAbsIntegrable.proof Seg.SliceMassFinite GroundTheory.Heights₂.Heights.SegreChartSheetCompare.proof

theorem Seg.PtsSemiPosMassFinite : GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.proof Seg.PtsPosPartProjIndep Seg.PtsSegreChartFibreSum Seg.SegreChartAbsIntegrable

theorem Seg.PtsPosDensIntegrable : GroundTheory.Heights₂.Heights.PtsPosDensIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.PtsPosDensIntegrable.proof Seg.PtsSemiPosMassFinite

theorem Seg.PtsIntegralProjIndep : GroundTheory.Heights₂.Heights.PtsIntegralProjIndep.Statement :=
  @GroundTheory.Heights₂.Heights.PtsIntegralProjIndep.proof Seg.PtsPosDensIntegrable Seg.PtsPosPartProjIndep

theorem Seg.PtsIntegralSegreChartProj : GroundTheory.Heights₂.Heights.PtsIntegralSegreChartProj.Statement :=
  @GroundTheory.Heights₂.Heights.PtsIntegralSegreChartProj.proof GroundTheory.Heights₂.Heights.SegreChartProjFinite.proof GroundTheory.Heights₂.Heights.SegreChartZeroSet.proof Seg.SegreChartAbsIntegrable Seg.PtsSegreChartFibreSum

theorem Seg.SegreChartIntegral : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement :=
  @GroundTheory.Heights₂.Heights.SegreChartIntegral.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SegreCoordGoodProj Seg.PtsIntegralProjIndep Seg.PtsIntegralSegreChartProj

theorem Seg.SegreChart : GroundTheory.Heights₂.Heights.SegreChart.Statement :=
  @GroundTheory.Heights₂.Heights.SegreChart.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.SegreChartDim Seg.SegreChartIntegral

theorem thmIExists (hPL : PoincareLelong) (hE : ReciprocityTheory.ChartRestriction.G.Geo.ResExistsStatement) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement := by
  have hInt : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement := ForSecondHalf.PtsIntegrable.of_resExists hE
  have hAbs : Inter.PtsAbsIntegrable.Statement :=
    Inter.PtsAbsIntegrable.proof hInt (Inter.PtsAbsMeasurable.proof hE)
  have hBil : PtsBilinear.Statement := PtsBilinear.proof hAbs PtsSumMeasurable.proof
  have hSt : ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement :=
    StokesStatement.of_found hBil HilbertSamuel.Closed.SegrePartition Seg.SegreChart
      AutoClose.StokesOnVariety
  have hLe : Inter.DeLeSemiPos.Statement :=
    Inter.DeLeSemiPos.proof hPL hSt (Inter.PtsAddFirst.proof hInt) (Inter.PtsRegLimit.proof hInt hAbs)
      (Inter.PtsMonoSemiPos.of_remaining hInt) Inter.RegCurvBound.full Inter.HorizNotMem.full
  have hPL2 : ReciprocityTheory.ChartRestriction.G.Geo.SectionSpaceSymmetry :=
    Inter.ProjectiveLineTwo.proof (Inter.DeSlotAdd.proof hE) Inter.SemiPosTwist.full hLe
  have hSwap : Inter.Swap.Statement := Inter.Swap.proof Inter.SwapCycles.full Inter.GeoNumCut.full hPL2
  have hRS : Inter.RPositionAdd.Statement := Inter.RPositionAdd.of_remaining hInt
  have hSymm : Inter.ThmISymm.Statement :=
    Inter.ThmISymm.proof hSwap hRS fibreComp
      (fun p _ K _ ι _ => Targets.ExistsUnique.full (ZMod p) ι)
      (fun p _ K _ ι _ => Targets.SymmStatement.of_type (ZMod p) ι)
      (fun K _ ι _ => GroundTheory.Heights₂.Heights.geoNumStatement ι)
  exact Inter.ThmIExists.proof AutoClose.Inter_R1Indep (Inter.RMul.proof hInt)
    (Inter.WellDefined.proof hSwap hRS) hSymm

end GlobalTheory.CompanionTheory.Ar.Pub
