import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoOfEqualSublinesShortExact
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_of_equal_sublines_shortExact : ∀ (X : Scheme.{0}) (V L Q L' Q' : X.Modules) (l : L ⟶ V) (m : V ⟶ Q) (w : l ≫ m = 0) (l' : L' ⟶ V) (m' : V ⟶ Q') (w' : l' ≫ m' = 0), (ShortComplex.mk l m w).ShortExact → (ShortComplex.mk l' m' w').ShortExact → IsVB Q 1 → IsVB Q' 1 → l' ≫ m = 0 → ∃ e : L' ≅ L, e.hom ≫ l = l' := by
  first | exact @GlobalTheory.SameLine.eq_line | exact GlobalTheory.SameLine.eq_line | (intros; apply GlobalTheory.SameLine.eq_line <;> assumption)
