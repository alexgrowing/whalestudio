import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.InhabitedChartFracSeparable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartNormAlgClosed
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLocalSheets
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapArea
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCycleAverage
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.UniformIntegrabilityProportionalityHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.ObjectsChowIntChowFormExists
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.TargetsProjFullRankMeetsRegular
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergySymm
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutCaseSharp
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutPrimeEq
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointInj
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointNagata
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Imports
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveSectionQuotLocal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointLength
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjFullRankDense
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjRegularClosureOpen
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetSimpleNull
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.ChartEnergySymm : GroundTheory.Heights₂.Heights.ChartEnergySymm.Statement :=
  @GroundTheory.Heights₂.Heights.ChartEnergySymm.proof GroundTheory.Heights₂.Heights.AutoClose.ChartIbpSymm

theorem GroundTheory.Heights₂.Heights.AutoClose.VertPointInj : GroundTheory.Heights₂.Heights.VertPointInj.Statement :=
  @GroundTheory.Heights₂.Heights.VertPointInj.proof GroundTheory.Heights₂.Heights.AutoClose.VertPointChart

theorem GroundTheory.Heights₂.Heights.AutoClose.RestCutCaseSharp : GroundTheory.Heights₂.Heights.RestCutCaseSharp.Statement :=
  @GroundTheory.Heights₂.Heights.RestCutCaseSharp.proof GroundTheory.Heights₂.Heights.RestTerms.RestBound.full GroundTheory.Heights₂.Heights.AutoClose.RestCutCaseCompare GroundTheory.Heights₂.Heights.AutoClose.RestCutCaseDecomp GroundTheory.Heights₂.Heights.AutoClose.RestCutTermEq GroundTheory.Heights₂.Heights.RestCutPrimeEq.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.VertPointNagata : GroundTheory.Heights₂.Heights.VertPointNagata.Statement :=
  @GroundTheory.Heights₂.Heights.VertPointNagata.proof GroundTheory.Heights₂.Heights.AutoClose.VertPointChart

theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_CurveVertPointLength : GroundTheory.Heights₂.Heights.Targets.CurveVertPointLength.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.CurveVertPointLength.proof GroundTheory.Heights₂.Heights.AutoClose.Targets_CurveVertPointChart GroundTheory.Heights₂.Heights.AutoClose.Targets_CurveVertPointInj GroundTheory.Heights₂.Heights.AutoClose.Targets_CurveVertPointSurj GroundTheory.Heights₂.Heights.AutoClose.Targets_CurveVertPointMultChart GroundTheory.Heights₂.Heights.Targets.CurveSectionQuotLocal.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_ProjFullRankDense : GroundTheory.Heights₂.Heights.Targets.ProjFullRankDense.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ProjFullRankDense.of_found GroundTheory.Heights₂.Heights.Targets.ProjRegularClosureOpen.proof GroundTheory.Heights₂.Heights.AutoClose.Targets_ProjFullRankMeetsRegular

theorem GroundTheory.Heights₂.Heights.AutoClose.PtsSheetSimpleNull : GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.proof GroundTheory.Heights₂.Heights.AutoClose.PtsGenericCount

theorem GroundTheory.Heights₂.Heights.AutoClose.CycleAverage : GroundTheory.Heights₂.Heights.CycleAverage.Statement :=
  @GroundTheory.Heights₂.Heights.CycleAverage.proof GroundTheory.Heights₂.Heights.AutoClose.ConeAverage

theorem GroundTheory.Heights₂.Heights.AutoClose.ConeMapArea : GroundTheory.Heights₂.Heights.ConeMapArea.Statement :=
  @GroundTheory.Heights₂.Heights.ConeMapArea.proof GroundTheory.Heights₂.Heights.AutoClose.ConeMapAreaOne

theorem GroundTheory.Heights₂.Heights.AutoClose.ChartNormAlgClosed : GroundTheory.Heights₂.Heights.ChartNormAlgClosed.Statement :=
  @GroundTheory.Heights₂.Heights.ChartNormAlgClosed.proof GroundTheory.Heights₂.Heights.IncIdealBelow.full GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.full GroundTheory.Heights₂.Heights.LocalizationPrimeDVR.full GroundTheory.Heights₂.Heights.ChartFinite.full GroundTheory.Heights₂.Heights.ChartFracSeparableInhabited.chartLocDomain GroundTheory.Heights₂.Heights.ChartFirstGroupPrime.full GroundTheory.Heights₂.Heights.ChartFirstGroupDvd.full GroundTheory.Heights₂.Heights.AutoClose.NormOfDividedFormSep GroundTheory.Heights₂.Heights.AutoClose.ChartFracSeparable

theorem GroundTheory.Heights₂.Heights.AutoClose.ConeLocalSheets : GroundTheory.Heights₂.Heights.ConeLocalSheets.Statement :=
  @GroundTheory.Heights₂.Heights.ConeLocalSheets.proof GroundTheory.Heights₂.Heights.AutoClose.QuasiFiniteSheets
