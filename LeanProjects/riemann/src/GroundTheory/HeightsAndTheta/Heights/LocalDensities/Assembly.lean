import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PFlagWeightLevi
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PFlagRootProduct
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PDegreeRatio
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PRhoBound
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PHermitianDetMono
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PMongeAmpereCompactChange
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PMongeAmpereComparison
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PFubiniStudyCoverMass
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PIntegralPointThroughPrime
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PIntegralOnModel
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PKrullHeightOne
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PRiemannExtension
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Imports
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.OneChartAtlasIndexEq
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.OpenAtlasSymmEventuallyEq
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.OfFubiniStudyCoverMass
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.NormLeOneIffIsIntegralElemOfEquiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

theorem FlagWeightLevi.full : FlagWeightLevi.Statement :=
  FlagWeightLevi.proof

theorem FlagRootProduct.full : FlagRootProduct.Statement :=
  FlagRootProduct.proof

theorem DegreeRatio.full : DegreeRatio.Statement :=
  DegreeRatio.proof

theorem RhoBound.full : RhoBound.Statement :=
  RhoBound.proof DegreeRatio.full

theorem HermitianDetMono.full : HermitianDetMono.Statement :=
  HermitianDetMono.proof

theorem MongeAmpereCompactChange.full : MongeAmpereCompactChange.Statement :=
  MongeAmpereCompactChange.proof

theorem MongeAmpereComparison.full : MongeAmpereComparison.Statement :=
  MongeAmpereComparison.proof MongeAmpereCompactChange.full

theorem FubiniStudyCoverMass.of_open (hFS : FubiniStudyChartDensity.Statement)
    (hPart : ChartPartitionExists.Statement) (hCov : CoverChartLIntegral.Statement) :
    FubiniStudyCoverMass.Statement :=
  FubiniStudyCoverMass.proof hFS hPart hCov

theorem CoverMass2.of_open (hFS : FubiniStudyChartDensity.Statement)
    (hPart : ChartPartitionExists.Statement) (hCov : CoverChartLIntegral.Statement) :
    IndefiniteRowSideFullHecke.FourB.CoverMass2.Statement :=
  CoverMass2.of_fubiniStudyCoverMass (FubiniStudyCoverMass.proof hFS hPart hCov)

theorem IntegralOnModel.of_open (h₁ : ClosedPointOfGenericFibre.Statement)
    (h₂ : IntegralPointOfAlgebraicDomain.Statement) : IntegralOnModel.Statement :=
  IntegralOnModel.proof (IntegralPointThroughPrime.proof h₁ h₂)

end GroundTheory.Heights₂.Heights.FourB

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

theorem KrullHeightOne.full : KrullHeightOne.Statement :=
  KrullHeightOne.proof

theorem DetMono.full : DetMono.Statement :=
  GroundTheory.Heights₂.Heights.DetMono.equiv.mp _root_.GroundTheory.Heights₂.Heights.FourB.HermitianDetMono.full

theorem MACompact.full : MACompact.Statement :=
  MACompact.of_manifold _root_.GroundTheory.Heights₂.Heights.FourB.MongeAmpereCompactChange.full

theorem MAComparison.full : MAComparison.Statement :=
  MAComparison.of_manifold _root_.GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison.full

theorem RiemannExt.of_open (hZ : ZariskiDense.Statement) : RiemannExt.Statement :=
  RiemannExt.proof KrullHeightOne.full hZ

theorem Normality.of_open
    (h₁ : _root_.GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre.Statement)
    (h₂ : _root_.GroundTheory.Heights₂.Heights.FourB.IntegralPointOfAlgebraicDomain.Statement) :
    Normality.Statement :=
  Normality.of_integralOnModel (_root_.GroundTheory.Heights₂.Heights.FourB.IntegralOnModel.of_open h₁ h₂)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
