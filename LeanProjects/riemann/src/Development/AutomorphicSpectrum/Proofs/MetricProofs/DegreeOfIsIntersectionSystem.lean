import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.ConservationDegreeFormOfExistence

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem degree_of_isIntersectionSystem (II : IntersectionSystem) (hII : IsIntersectionSystem II) :
    ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement :=
  GroundTheory.Heights₂.Heights.Inter.Conservation.conservation_iff_degree_statement.mp
    (GroundTheory.Heights₂.Heights.Inter.Conservation.conservation_degree_form_of_existence ⟨II, hII⟩
      GroundTheory.Heights₂.Heights.Inter.Conservation.statement_holds)

theorem degree_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement :=
  fun ⟨II, hII⟩ => degree_of_isIntersectionSystem II hII.1

end GlobalTheory.CompanionTheory.Ar.Giv
