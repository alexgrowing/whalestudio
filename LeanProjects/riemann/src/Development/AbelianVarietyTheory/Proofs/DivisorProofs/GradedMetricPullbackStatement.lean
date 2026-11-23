import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_metric_pullback : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (w : π ≫ p = q) (ι : Type) (L : X.Modules) (g : ℕ) (hL : VMetric p L g) (E E' : ι → X.Modules) (r : ι → ℕ) (h : ∀ a, VMetric p (E a) (r a)) (u : ∀ a, E a ⟶ E' a) (m : ℕ) (o : ι ≃ Fin m), (∀ a, IsVB (E' a) (r a)) → IsGraded hL o h u → IsGraded (E' := fun a => (Scheme.Modules.pullback π).obj (E' a)) (hL.pull π w) o (fun a => (h a).pull π w) fun a => (Scheme.Modules.pullback π).map (u a) := by
  first | exact @GlobalTheory.OrthFilt.isGraded_pull | exact GlobalTheory.OrthFilt.isGraded_pull | (intros; apply GlobalTheory.OrthFilt.isGraded_pull <;> assumption)
