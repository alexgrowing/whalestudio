import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.HsLinksOfUse
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LineOfLargeDegreeOfMoriwaki
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights in

theorem lineOfLargeDegree_of_use :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
        GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement := by
  intro hAIS hU hBig hResK
  have hZ2 : SuccessiveMinimaUpperBound := (hsLinks_of_use hU hBig).2.2.1
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
  exact LineOfLargeDegreeFromZ.ofOpen hVRI hSN hEnergy hBasis hStacked hSDeg hBC
    (GrassLinesProj.proof (GlobalTheory.T.coordinate_projection_of_arith_system hAIS))
    (DualGeomDegCharts.proof ChartDensityIntegrable.proof) GrassGeomDegChart.proof ChartMassInvariant.proof
    (degree_of_system hAIS) hInd hU.z1 hZ2 hI

end GlobalTheory.CompanionTheory.Ar.Giv
