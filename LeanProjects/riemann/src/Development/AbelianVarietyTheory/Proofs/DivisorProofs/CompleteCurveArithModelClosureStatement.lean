import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteCurveArithModelClosure
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_curve_arith_model_closure : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (P : TrueGeo.Model Y) (Z : Closeds Y.X), IsCompleteCurve F Z → ∃ (W : Scheme.{0}) (w : W ⟶ P.X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsClosedImmersion w ∧ IsArithVar (w ≫ P.p) 1 ∧ z ≫ w = redι Z ≫ P.j ∧ IsPullback z (redι Z ≫ Y.str) (w ≫ P.p) (spMap (algebraMap (𝓞 F) F)) := by
  first | exact @GlobalTheory.CurveClosure.exists_closure_arith_surface | exact GlobalTheory.CurveClosure.exists_closure_arith_surface | (intros; apply GlobalTheory.CurveClosure.exists_closure_arith_surface <;> assumption)
