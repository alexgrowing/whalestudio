import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNowhereZeroSectionLineBundlePowFiniteInt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nowhereZero_section_lineBundle_pow_finite_int : ∀ (T : Scheme.{0}) [IsAffine T] [AlgebraicGeometry.IsReduced T], Module.Finite ℤ Γ(T, ⊤) → ∀ L : LB T, L.IsLB → ∃ (n : ℕ) (s : (lbPow L n).Sec), 1 ≤ n ∧ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ := by
  first | exact @GlobalTheory.PowNowhereZero.main | exact GlobalTheory.PowNowhereZero.main | (intros; apply GlobalTheory.PowNowhereZero.main <;> assumption)
