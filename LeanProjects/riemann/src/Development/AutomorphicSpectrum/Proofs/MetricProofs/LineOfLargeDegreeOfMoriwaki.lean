import Mathlib
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PLineOfLargeDegreeX
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopBasisChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PIntCoordChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PIntCoordGeoNum
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PIntCoordArInt
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopStacked
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopSimpleSub
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopSimpleStacked
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedGraphImage
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedGraphHorizontal
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedGraphFibre
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcCycle
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcReduced
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcGeoSecond
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcLinear
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcResidueExists
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeModPrime
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcBaseLe
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcLinPrimeLe
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualCotangentKer
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinPrimeCut
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinPrimeBase
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcGeoFirst
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassFibreDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdBaseChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdBasePtFree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdImageBot
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdMetricPull
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassLinesProj
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassGeomDegChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartMassInvariant
import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterOsgood
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBridge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIsomInvariance
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphIsometric
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HsLinksOfMoriwaki
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionExistsOfArithSystemStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateProjectionOfArithSystemStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalBaseStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedGraphBihomogeneousStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalChartStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalCoordsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalLeadingFormStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystemStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatementStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatementStatement
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertRIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLogCardLength
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSectionQuotFinite
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSectionIndexNorm
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualMetricEnergy
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualGeomDegCharts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartDensityIntegrable
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdGenDeg
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.POneBlockPointDeg
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointLength
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSectionQuotLocal
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointResidue
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCurveCharts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PInvertibleIdealIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.POrderIdealIndexExtension
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLocallyPrincipalCoprime
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualEnergyCharts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergy
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdFibreRatios
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGenFibreModelTransport
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdGraphModel
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdModelRank
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdModelTransc
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointInj
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointSurj
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointMultChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PClosedPointChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PClosedPointUnitSection
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyIntegrable
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PHermFormCompare
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyInvariant
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergySwap
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyDiagonal
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointNagata
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartHessCompare
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyCocycle
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergySymm
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartIbpSymm
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartIbpCutoff
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartCutoffEnergy
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartDiffEnergy
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights in

theorem lineOfLargeDegree_of_moriwaki :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
        GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement := by
  intro hAIS hHS hBig hResK
  have hZ2 : SuccessiveMinimaUpperBound := (hsLinks_of_moriwaki hHS hBig).2.2.1
  have hI : ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement := GlobalTheory.T.intersection_exists_of_arith_system hAIS
  have hGr : GraphStatement := GlobalTheory.T.graph_statement_holds
  have hAI3 : Inter.PushforwardArithIntersection.Statement := GlobalTheory.T.generic_degree_of_arith_system hAIS
  have hPts : PtsIntegrableStatement := GlobalTheory.T.points_integrable_of_resolution_statement hResK
  have hInd : PtsIndepStatement :=
    ReciprocityTheory.ChartRestriction.G.Geo.ptsIndep_of (GlobalTheory.T.resolution_exists_of_resolution_statement hResK) HilbertSamuel.Closed.ReciprocityTheory.ChartRestriction.G.Geo.ResBridge
  have hSheet : SheetIndepStatement :=
    ReciprocityTheory.ChartRestriction.G.Geo.sheetIndep_of ReciprocityTheory.ChartRestriction.G.Geo.osgood
      HilbertSamuel.Closed.ReciprocityTheory.ChartRestriction.G.Geo.FibreFinite
  have hChange : IntCoordChange.Statement :=
    IntCoordChange.proof Inter.Closed.ReciprocityTheory.ChartRestriction.G.AI.I2.Unique IntCoordGeoNum.proof
      (IntCoordArInt.proof hInd hSheet)
  have hBasis : DualTopBasisChange.Statement := DualTopBasisChange.proof hChange
  have hSDeg : DualStackedDegree.Statement := DualStackedDegree.proof DualLatticeIndex.proof
  have hCC : CurveCharts.Statement :=
    CurveCharts.proof (ClosedPointChart.proof ClosedPointUnitSection.proof)
  have hVPC : VertPointChart.Statement := VertPointChart.proof hCC
  have hVRI : VertRIndex.Statement :=
    VertRIndex.proof LogCardLength.proof SectionQuotFinite.closed
      (VertPointLength.proof hVPC (VertPointInj.proof hVPC)
        (VertPointSurj.proof hCC SectionQuotLocal.proof)
        (VertPointMultChart.proof hVPC (VertPointNagata.proof hVPC)) SectionQuotLocal.proof)
      (VertPointResidue.proof hCC)
  have hSN : SectionIndexNorm.Statement :=
    SectionIndexNorm.proof hCC
      (InvertibleIdealIndex.proof OrderIdealIndexExtension.proof LocallyPrincipalCoprime.proof)
  have hCELI : ChartEnergyLinearInvariant.Statement :=
    ChartEnergyLinearInvariant.proof ChartEnergySwapInvariant.proof
  have hCE : ChartEnergy.Statement :=
    ChartEnergy.proof hCELI
      (ChartEnergyDiagonal.proof hCELI
        (ChartEnergyCocycle.proof
          (ChartEnergySymm.proof
            (ChartIbpSymm.proof
              (ChartIbpCutoff.proof ChartCutoffEnergy.proof
                (ChartDiffEnergy.proof ChartCutoffEnergy.proof))))))
  have hEnergy : DualMetricEnergy.Statement :=
    DualMetricEnergy.proof
      (DualEnergyCharts.proof
        (ChartEnergyIntegrable.proof HermFormCompare.proof
          (ChartHessCompare.proof HermFormCompare.proof)))
      hCE GrassGeomDegChart.proof ChartMassInvariant.proof
  have hStdGenDeg : DualStdGenDeg.Statement :=
    DualStdGenDeg.proof OneBlockPointDeg.proof
      (DualStdFibreRatios.proof GenFibreModelTransport.proof DualStdGraphModel.proof
        DualStdModelRank.proof DualStdModelTransc.proof)
  have hLinear : DualStackedExcLinear.Statement :=
    DualStackedExcLinear.proof (DualStackedExcResidueExists.proof DualLatticeModPrime.proof)
      (DualStackedExcBaseLe.proof GlobalTheory.T.dual_stacked_graph_bihomogeneous GlobalTheory.T.dual_stacked_exceptional_leading_form)
      (DualStackedExcLinPrimeLe.proof DualCotangentKer.proof)
  have hFib : DualStackedGraphFibre.Statement :=
    DualStackedGraphFibre.proof
      (DualStackedExcCycle.proof
        (DualStackedExcReduced.proof GlobalTheory.T.dual_stacked_exceptional_coords GlobalTheory.T.dual_stacked_exceptional_base GlobalTheory.T.dual_stacked_exceptional_chart))
      (DualStackedExcGeoSecond.proof hLinear LinPrimeCut.proof LinPrimeBase.proof)
      DualStackedExcGeoFirst.proof
  have hStep : DualTopSimpleStacked.Statement :=
    DualTopSimpleStacked.proof hAI3 hGr (DualStackedGraphImage.proof hGr GlobalTheory.CompanionTheory.Ar.Giv.fibreDim)
      DualStackedGraphHorizontal.proof hFib GrassFibreDegree.proof
  have hStacked : DualTopStacked.Statement :=
    DualTopStacked.proof (DualTopSimpleSub.proof hBasis hStep hSDeg) hBasis hSDeg
  have hCM : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement :=
    Targets.ChangeOfModel.of_found hAI3 hGr
      (HilbertSamuel.IsomInvariance.proof (Inter.RatR.proof hPts))
      HilbertSamuel.GraphIsometric.proof
  have hBC : DualStdBaseChange.Statement :=
    DualStdBaseChange.proof hCM hGr Targets.genFibreExists
      (fun F _ K _ ι _ => Targets.ExistsUnique.full F ι)
      DualStdBasePtFree.proof DualStdImageBot.proof hStdGenDeg DualStdMetricPull.proof
  exact LineOfLargeDegree.proof hHS hZ2 hI hVRI hSN
    hEnergy hBasis hStacked hSDeg hBC (GrassLinesProj.proof (GlobalTheory.T.coordinate_projection_of_arith_system hAIS))
    (DualGeomDegCharts.proof ChartDensityIntegrable.proof) GrassGeomDegChart.proof ChartMassInvariant.proof
    (degree_of_system hAIS) hInd

end GlobalTheory.CompanionTheory.Ar.Giv
