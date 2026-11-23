import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfInjOn
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalRep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantShift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HilbertSamuelG7OfMoriwakiStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PackingStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem selfIntersection_le_of_boundedInjection :
    MoriwakiHSStatement → MoriwakiBigStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.G3.Statement :=
  fun hHS hBig =>
    GroundTheory.Heights₂.Heights.HilbertSamuel.G3.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.LocalRep.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantShift.proof
      (GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeBig.of_moriwakiBig_only hBig)
      (GlobalTheory.T.hilbert_samuel_G7_of_moriwaki hHS) GlobalTheory.T.packing'

end GlobalTheory.CompanionTheory.Ar.Giv
