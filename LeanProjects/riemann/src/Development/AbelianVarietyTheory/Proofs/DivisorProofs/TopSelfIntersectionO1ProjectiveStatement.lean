import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionO1Projective
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_self_intersection_O1_projective : ∀ (k : Type) [Field k] (N : ℕ), letI := GlobalTheory.algebraΓOfHom (PSpace.str k N); topSelfIntersection k (ProjSpace.O1 k N) N = 1 := by
  first | exact @GlobalTheory.ProjSpaceDegree.topSelf_O1_str | exact GlobalTheory.ProjSpaceDegree.topSelf_O1_str | (intros; apply GlobalTheory.ProjSpaceDegree.topSelf_O1_str <;> assumption)
