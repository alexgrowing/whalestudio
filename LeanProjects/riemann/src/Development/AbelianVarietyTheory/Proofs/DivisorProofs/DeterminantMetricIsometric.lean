import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory

namespace VMetric

theorem isometric_det_of_isIsometry : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E E' : X.Modules) (r : ℕ) (h : VMetric p E r) (h' : VMetric p E' r) (φ : E ≅ E') (H : h.IsCInf) (H' : h'.IsCInf), h.IsIsometry h' φ → (VMetric.det H).Isometric (VMetric.det H') := by
  intro k _ X p E E' r h h' φ H H' hφ
  rw [isIsometry_iff] at hφ
  subst hφ
  exact isometric_det_map H φ

end VMetric

end GlobalTheory
