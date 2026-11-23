import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricRestrictionVanishingLocus
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_metric_restriction_vanishing_locus : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (V L Q L' : X.Modules) (l : L ⟶ V) (m : V ⟶ Q) (w : l ≫ m = 0) (l' : L' ⟶ V), (ShortComplex.mk l m w).ShortExact → IsVB Q 1 → ∀ (hL : IsVB L 1) (hL' : IsVB L' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l') (h : VMetric p V (1 + 1)) (H : h.IsCInf) (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ X), VanishesAt (l' ≫ m) (i (genericPoint Z)) → ((VMetric.det (H.restrict hl hL)).restr i).Isometric ((VMetric.det (H.restrict hl' hL')).restr i) := by
  first | exact @GlobalTheory.CurveDens.isometric_restr_of_vanishesAt | exact GlobalTheory.CurveDens.isometric_restr_of_vanishesAt | (intros; apply GlobalTheory.CurveDens.isometric_restr_of_vanishesAt <;> assumption)
