import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointSumOverResidues
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_point_sum_over_residues : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [Finite (k →+* ℂ)] (S : Finset X) (m : X → ℝ), (∀ x ∈ S, Finite (X.residueField x →+* ℂ)) → (∀ x : X, CharZero (X.residueField x) → m x ≠ 0 → x ∈ S) → ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts p σ, m y.pt = ∑ x ∈ S, m x * (Nat.card (X.residueField x →+* ℂ) : ℝ) := by
  first | exact @GlobalTheory.finsum_cxPts_eq_sum_card | exact GlobalTheory.finsum_cxPts_eq_sum_card | (intros; apply GlobalTheory.finsum_cxPts_eq_sum_card <;> assumption)
