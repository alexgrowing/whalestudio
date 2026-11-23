import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothProjVarietyCompactManifold
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
theorem _root_.GlobalTheory.T.complexPoints_smoothProjVariety_compact_manifold : ∀ Y : Var ℂ, CompactSpace (CxPts Y.str (RingHom.id ℂ)) ∧ T2Space (CxPts Y.str (RingHom.id ℂ)) ∧ SecondCountableTopology (CxPts Y.str (RingHom.id ℂ)) ∧ ∃ A : FinHolAtlas Y.dim (CxPts Y.str (RingHom.id ℂ)), IsAlgAtlas A := by
  first | exact @GlobalTheory.cxPts_var_compact_manifold | exact GlobalTheory.cxPts_var_compact_manifold | (intros; apply GlobalTheory.cxPts_var_compact_manifold <;> assumption)
