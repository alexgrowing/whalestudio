import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelongInv
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PoincareLelongAlt
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PotFinCons
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LogRegLineTensor
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongSectionLimit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongChartLimit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsIntegrable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Stokes
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsBilinear
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChart
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartSectionNotMem
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongWeightLimit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLocalMultComap
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PVarIntGraphX
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOnVariety
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOff
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffTube
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeEuclMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepRankOne
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepAreaCount
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOnZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitGoodPoints
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongMassNearSmall
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.CentredDiscCoverCurveHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.UniformIntegrabilityProportionalityHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.IsolatedPointsCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisor
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartIntegral

namespace PositivityTheory.Tls2.Pl

open GroundTheory.Heights₂.Heights

theorem stokesOnVariety : GroundTheory.Heights₂.Heights.StokesOnVariety.Statement := by
  have hDeep : TubeDeepMass.Statement :=
    TubeDeepMass.proof TubeDeepRankOne.proof
      (TubeDeepAreaCount.proof AutoClose.IsolatedPointsCount)
      HilbertSamuel.Closed.TubeDeepWeightMass
  exact StokesOnVariety.of_open HilbertSamuel.Closed.SheetImageAreaSet
    (TubeEuclMass.proof HilbertSamuel.Closed.TubeCollarMass hDeep)

theorem lelongLimit (hBr : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement)
    (hLim : GroundTheory.Heights₂.Heights.LelongLimitAtBranches.Statement)
    (hOrd : GroundTheory.Heights₂.Heights.LocalOrder.Statement)
    (hReg : GroundTheory.Heights₂.Heights.RegMassNearSmall.Statement) :
    GroundTheory.Heights₂.Heights.LelongLimit.Statement := by
  have hGood : LelongLimitGoodPoints.Statement := LelongLimitGoodPoints.proof hBr hLim hOrd
  have hMass : LelongMassNearSmall.Statement :=
    LelongMassNearSmall.proof hReg AutoClose.VarMassNearSmall
  exact LelongLimit.proof AutoClose.LelongLimitOffZero
    (LelongLimitOnZero.proof AutoClose.LelongLimitOffZero hGood hMass AutoClose.VarIntAdd)
    AutoClose.VarIntAdd

theorem lelongPolyLimit (hL : GroundTheory.Heights₂.Heights.LelongLimit.Statement) :
    GroundTheory.Heights₂.Heights.Targets.LelongPolyLimit.Statement :=
  GroundTheory.Heights₂.Heights.Targets.LelongPolyLimit.of_mult_weight GroundTheory.Heights₂.Heights.Targets.LocalMultComap.proof
    (GroundTheory.Heights₂.Heights.Targets.LelongWeightLimit.proof hL stokesOnVariety
      GroundTheory.Heights₂.Heights.AutoClose.Targets_LelongWeightDiff)

theorem ptsAbsMeasurable (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement) :
    GroundTheory.Heights₂.Heights.Inter.PtsAbsMeasurable.Statement :=
  fun K _ ι _ P e Ψ L A s h1 h2 h3 h4 h5 => (hAbs K ι P e Ψ L A s h1 h2 h3 h4 h5).aestronglyMeasurable

theorem poincareLelong_of (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (hSCI : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement)
    (hCDC : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement)
    (hLPL : GroundTheory.Heights₂.Heights.Targets.LelongPolyLimit.Statement) : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong := by
  have hPI : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement :=
    PtsIntegrable.of_found hAbs HilbertSamuel.Closed.PtsSumMeasurable
  have hStk : ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement :=
    StokesStatement.of_found (PtsBilinear.proof hAbs HilbertSamuel.Closed.PtsSumMeasurable)
      HilbertSamuel.Closed.SegrePartition
      (SegreChart.proof HilbertSamuel.Closed.SegreChartDim hSCI) stokesOnVariety
  have hChart : Targets.LelongChartLimit.Statement :=
    Targets.LelongChartLimit.proof hSCI HilbertSamuel.Closed.SegreChartDim
      Targets.ChartSectionNotMem.proof hLPL hCDC
  exact Targets.PoincareLelongAlt.of_found hStk (Targets.PoincareLelongRegularised.proof hPI (ptsAbsMeasurable hAbs))
    (Targets.PoincareLelongLimit.proof hPI (Targets.LelongSectionLimit.proof hPI hChart))

theorem poincareLelong_of_leaves (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (hSCI : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement)
    (hCDC : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement)
    (hBr : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement)
    (hLim : GroundTheory.Heights₂.Heights.LelongLimitAtBranches.Statement)
    (hOrd : GroundTheory.Heights₂.Heights.LocalOrder.Statement)
    (hReg : GroundTheory.Heights₂.Heights.RegMassNearSmall.Statement) : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong :=
  poincareLelong_of hAbs hSCI hCDC (lelongPolyLimit (lelongLimit hBr hLim hOrd hReg))

theorem poincareLelongInv_of_leaves (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (hSCI : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement)
    (hCDC : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement)
    (hBr : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement)
    (hLim : GroundTheory.Heights₂.Heights.LelongLimitAtBranches.Statement)
    (hOrd : GroundTheory.Heights₂.Heights.LocalOrder.Statement)
    (hReg : GroundTheory.Heights₂.Heights.RegMassNearSmall.Statement) : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv := by
  intro K _ ι _ P n L A B s hP hL hA hB _ _ _ hB0 hs
  have h : ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticPoincareLelongFormula :=
    poincareLelong_of_leaves hAbs hSCI hCDC hBr hLim hOrd hReg
  exact h K ι P n L A B s hP hL hA hB hB0 hs

end PositivityTheory.Tls2.Pl
