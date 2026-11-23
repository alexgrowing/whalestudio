import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreePullbackEqReducedIntersectionNumbe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOfSemipositiveFibrewise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveModelRationalDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFibreProjectiveCurve
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
open Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalDegree_pullback_eq_reducedIntersectionNumber : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (Z : Closeds (ratFibre p)), IsCompleteCurve ℚ Z → ∀ (W : Scheme.{0}) (w : W ⟶ X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsArithVar (w ≫ p) 1 → z ≫ w = redι Z ≫ ratFibre.fst p → IsPullback z (redι Z ≫ ratFibre.snd p) ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) → ∀ M : LB X, M.IsLB → ratDeg (w ≫ p) (M.pull w) = interNumRed ℚ Z ![M.pull (ratFibre.fst p)] := by
  first | exact @GlobalTheory.RatFibreClosure.ratDeg_pull_eq_interNumRed | exact GlobalTheory.RatFibreClosure.ratDeg_pull_eq_interNumRed | (intros; apply GlobalTheory.RatFibreClosure.ratDeg_pull_eq_interNumRed <;> assumption)
