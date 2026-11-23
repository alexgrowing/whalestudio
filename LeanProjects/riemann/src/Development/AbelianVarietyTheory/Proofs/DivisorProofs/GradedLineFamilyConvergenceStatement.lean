import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedLineFamilyConvergence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_line_family_convergence : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E : X.Modules) (r : ℕ) (t : ℝ → ℝ) (h : ℝ → VMetric p E r) (h₀ : VMetric p E r) (H : ∀ R, (h R).IsCInf) (H₀ : h₀.IsCInf), VFam t h h₀ → ∀ (fl : Vert.Flag E r) (i : Fin r), LFam t (fun R => VMetric.grLB fl i (H R)) (VMetric.grLB fl i H₀) := by
  first | exact @GlobalTheory.MetFam.lFam_grLB | exact GlobalTheory.MetFam.lFam_grLB | (intros; apply GlobalTheory.MetFam.lFam_grLB <;> assumption)
