import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreeEqOrderSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_degree_eq_order_sum : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsProjCurve ℚ (ratFibre p) → ∀ (L : LB X) (hL : L.IsLB) (s : L.Sec), genericPoint X ∈ nonzeroLocus s → ∃ S : Finset X, (∀ x : X, CharZero (X.residueField x) → x ∉ nonzeroLocus s → x ∈ S) ∧ (∀ x ∈ S, Finite (X.residueField x →+* ℂ)) ∧ ratDeg p L = ∑ x ∈ S, (secOrd hL s x : ℤ) * (Nat.card (X.residueField x →+* ℂ) : ℤ) := by
  first | exact @GlobalTheory.RatDegZeros.ratDeg_eq_sum | exact GlobalTheory.RatDegZeros.ratDeg_eq_sum | (intros; apply GlobalTheory.RatDegZeros.ratDeg_eq_sum <;> assumption)
