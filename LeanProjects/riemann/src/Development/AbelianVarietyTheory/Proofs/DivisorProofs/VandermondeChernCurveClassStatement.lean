import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeChernCurveClass
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vandermonde_chern_curve_class : Hypotheses2 → HypothesesH → RegularAlteration → OnObj fun D O _ _ _ _ => ∀ R : ℝ, 2 ≤ R → O.Y.arDeg ∅ R ((∑ τ, (pSum τ 2 : Pol D.what₂.Tau O.Y.N)) * (lamA D.what₂.Tau O.Y.N O.Y.j ^ (dimGr D.what₂.Tau O.Y.N O.Y.j - 1) * (fibPt D.what₂.Tau O.Y.N O.Y.j - vdmCl D.what₂.Tau O.Y.N O.Y.j))) = O.Y.chern (invForm O.Y.j (fun _ => -(((O.Y.j : ℝ) - 1) / O.Y.j)) (fun _ => -(((O.Y.N : ℝ) - O.Y.j - 1) / ((O.Y.N : ℝ) - O.Y.j))) * curveCl D.what₂.Tau O.Y.N O.Y.j) := by
  first | exact @GlobalTheory.BcEigen.bcFlag_eq_chern | exact GlobalTheory.BcEigen.bcFlag_eq_chern | (intros; apply GlobalTheory.BcEigen.bcFlag_eq_chern <;> assumption)
