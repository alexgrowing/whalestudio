import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.OfMoriwakiHS
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

theorem LineOfLargeDegree.proof (hM : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement) (hZ2 : SuccessiveMinimaUpperBound)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement)
    (hVI : VertRIndex.Statement) (hSN : SectionIndexNorm.Statement)
    (hEnergy : DualMetricEnergy.Statement)
    (hBasis : DualTopBasisChange.Statement) (hStacked : DualTopStacked.Statement)
    (hSDeg : DualStackedDegree.Statement) (hBC : DualStdBaseChange.Statement)
    (hGL : GrassLinesProj.Statement) (hCharts : DualGeomDegCharts.Statement)
    (hGChart : GrassGeomDegChart.Statement) (hMass : ChartMassInvariant.Statement)
    (hDeg : DegreeStatement) (hInd : PtsIndepStatement) :
    LineOfLargeDegree.Statement :=
  LineOfLargeDegreeFromZ.ofOpen hVI hSN hEnergy hBasis hStacked hSDeg hBC hGL hCharts hGChart hMass
    hDeg hInd (LowerBoundFree.Z1.proof hM HilbertSamuel.BirationalModelExists.full) hZ2 hI

end GroundTheory.Heights₂.Heights
