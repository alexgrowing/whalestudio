import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiRankBounds.OfDegreeGeneric
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiRankBounds.OfUpper

namespace PositivityTheory.Pf1.MbRank

open GroundTheory.Heights₂.Heights.HilbertSamuel

theorem ShiftSectionsRankUpper.of_ais (hAIS : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement) :
    ShiftSectionsRankUpper.Statement :=
  ShiftSectionsRankUpper.of_degreeGeneric
    (GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS))

theorem ShiftVolumeBound.of_ais (hSep : ShiftSectionSeparation.Statement) (hCount : SeparatedSmallCount.Statement)
    (hAIS : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement) : ShiftVolumeBound.Statement :=
  ShiftVolumeBound.of_upper hSep hCount (ShiftSectionsRankUpper.of_ais hAIS)

end PositivityTheory.Pf1.MbRank
