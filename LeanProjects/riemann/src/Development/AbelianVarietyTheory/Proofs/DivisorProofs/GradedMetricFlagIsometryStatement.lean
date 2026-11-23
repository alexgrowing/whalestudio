import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricFlagIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_metric_flag_isometry : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (ι : Type) [Fintype ι] (L : X.Modules) (g : ℕ) (hL : VMetric p L g) (HL : hL.IsCInf) (E E' : ι → X.Modules) (r : ι → ℕ) (h : ∀ a, VMetric p (E a) (r a)) (h' : ∀ a, VMetric p (E' a) (r a)) (H' : ∀ a, (h' a).IsCInf) (u : ∀ a, E a ⟶ E' a) (m : ℕ) (o : ι ≃ Fin m), (∀ a, IsoHom (h a) (h' a) (u a)) → IsGraded hL o h u → ∀ (fl : ∀ a, Vert.Flag (E a) (r a)) (fl' : ∀ a, Vert.Flag (E' a) (r a)), (∀ a, Compat (u a) (fl a) (fl' a)) → ∃ (T : ∀ a, E a ⟶ L) (w : Vert.Flag L g) (e : (Σ a, Fin (r a)) ≃ Fin g), OrthEmb hL h T ∧ Adapted T fl w e ∧ ∀ z, (VMetric.grLB w (e z) HL).Isometric (VMetric.grLB (fl' z.1) z.2 (H' z.1)) := by
  first | exact @GlobalTheory.FlagConcat.exists_adapted_flag | exact GlobalTheory.FlagConcat.exists_adapted_flag | (intros; apply GlobalTheory.FlagConcat.exists_adapted_flag <;> assumption)
