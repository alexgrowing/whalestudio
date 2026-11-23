import Mathlib
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassPush
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HFl
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFSGeomDegPos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGrassmannPushOfInputsStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem grassmann_height_Z2_of_push : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement →
    SuccessiveMinimaUpperBound → GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement :=
  fun hIn hAI hZ2 =>
    GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.proof hZ2 (GlobalTheory.T.flag_grassmann_push_of_inputs hIn hAI)
      (GroundTheory.Heights₂.Heights.HilbertSamuel.FSGeomDegPos.proof hIn.degree
        GroundTheory.Heights₂.Heights.HilbertSamuel.MultiDegreePositive.full)

end GlobalTheory.CompanionTheory.Ar.Giv
