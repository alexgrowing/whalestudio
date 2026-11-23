import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantMetricIsometric
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.CurveDens

theorem det_isometric_of_isIsometry : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E E' : X.Modules) (r : ℕ) (h : VMetric p E r) (h' : VMetric p E' r) (H : h.IsCInf) (H' : h'.IsCInf) (φ : E ≅ E'), h.IsIsometry h' φ → (VMetric.det H).Isometric (VMetric.det H') := by
  intro k _ X p E E' r h h' H H' φ hφ
  exact VMetric.isometric_det_of_isIsometry k X p E E' r h h' φ H H' hφ

end GlobalTheory.CurveDens
