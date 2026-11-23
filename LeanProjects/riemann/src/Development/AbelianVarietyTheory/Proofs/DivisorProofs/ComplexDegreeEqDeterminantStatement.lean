import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexDegreeEqDeterminant
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
theorem _root_.GlobalTheory.T.complex_degree_eq_determinant : ∀ (k : Type) [CommRing k] (X S : Scheme.{0}) (p : X ⟶ Sp k) (i : S ⟶ X), IsArithVar (i ≫ p) 1 → ∀ (E : X.Modules) (r : ℕ), VB.IsVB E r → cxDeg (i ≫ p) ((Scheme.Modules.pullback i).obj E) r = topSelfIntersection ℂ (((VB.det E r).pull i).pull (cxFibre.fst (i ≫ p))) 1 := by
  first | exact @GlobalTheory.SurfDeg.cxDeg_pullback_eq_topSelf | exact GlobalTheory.SurfDeg.cxDeg_pullback_eq_topSelf | (intros; apply GlobalTheory.SurfDeg.cxDeg_pullback_eq_topSelf <;> assumption)
