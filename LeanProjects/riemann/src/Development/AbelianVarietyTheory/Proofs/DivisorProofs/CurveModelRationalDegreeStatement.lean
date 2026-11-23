import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveModelRationalDegree
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_model_rational_degree : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (P : TrueGeo.Model Y) (Z : Closeds Y.X), IsCompleteCurve F Z → ∀ (W : Scheme.{0}) (w : W ⟶ P.X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsArithVar (w ≫ P.p) 1 → z ≫ w = redι Z ≫ P.j → IsPullback z (redι Z ≫ Y.str) (w ≫ P.p) (spMap (algebraMap (𝓞 F) F)) → ∀ M : LB P.X, M.IsLB → ratDeg (w ≫ P.p) (M.pull w) = (Module.finrank ℚ F : ℤ) * interNumRed F Z ![M.pull P.j] := by
  first | exact @GlobalTheory.RatFibreClosure.ratDeg_eq_finrank_mul_interNumRed | exact GlobalTheory.RatFibreClosure.ratDeg_eq_finrank_mul_interNumRed | (intros; apply GlobalTheory.RatFibreClosure.ratDeg_eq_finrank_mul_interNumRed <;> assumption)
