import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntPullFubiniStudyEqZeroOfNotDominant
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
theorem _root_.GlobalTheory.T.chernInt_pull_fubiniStudy_eq_zero_of_not_specializes : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim) (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str), (∃ x : PSpace ℂ Y.dim, ¬ π (genericPoint Y.X) ⤳ x) → Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ (fun _ => 1) = 0 := by
  first | exact @GlobalTheory.chernInt_pull_fubiniStudy_eq_zero_of_not_dominant | exact GlobalTheory.chernInt_pull_fubiniStudy_eq_zero_of_not_dominant | (intros; apply GlobalTheory.chernInt_pull_fubiniStudy_eq_zero_of_not_dominant <;> assumption)
