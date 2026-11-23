import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTopologicalKrullDimDiffOpenLt
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
theorem _root_.GlobalTheory.T.exists_finite_topologicalKrullDim_diff_open_lt : ∀ (T : Type) [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T] [T0Space T] (Z : Set T), IsClosed Z → ∃ S : Set T, S.Finite ∧ ∀ U : Set T, IsOpen U → S ⊆ U → ∀ d : ℕ, (topologicalKrullDim Z < (d + 1 : ℕ) → topologicalKrullDim (Z \ U : Set T) < (d : ℕ)) := by
  first | exact @GlobalTheory.Div.exists_finite_topologicalKrullDim_diff_lt | exact GlobalTheory.Div.exists_finite_topologicalKrullDim_diff_lt | (intros; apply GlobalTheory.Div.exists_finite_topologicalKrullDim_diff_lt <;> assumption)
