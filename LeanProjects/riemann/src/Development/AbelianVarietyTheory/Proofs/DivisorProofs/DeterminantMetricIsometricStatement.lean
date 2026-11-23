import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantMetricIsometric
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_metric_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E E' : X.Modules) (r : ℕ) (h : VMetric p E r) (h' : VMetric p E' r) (φ : E ≅ E') (H : h.IsCInf) (H' : h'.IsCInf), h.IsIsometry h' φ → (VMetric.det H).Isometric (VMetric.det H') := by
  first | exact @GlobalTheory.VMetric.isometric_det_of_isIsometry | exact GlobalTheory.VMetric.isometric_det_of_isIsometry | (intros; apply GlobalTheory.VMetric.isometric_det_of_isIsometry <;> assumption)
