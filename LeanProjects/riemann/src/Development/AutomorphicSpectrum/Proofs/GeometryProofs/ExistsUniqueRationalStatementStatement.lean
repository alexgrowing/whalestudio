import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueRationalStatement
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_rational_statement : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat | exact GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat <;> assumption)
