import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDensityExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_density_exists : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∃ w : AlgChart p σ 1 → CxPts p σ → ℝ, IsDens w ∧ ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, 0 < w c y := by
  first | exact @GlobalTheory.CurveDens.exists_isDens_pos | exact GlobalTheory.CurveDens.exists_isDens_pos | (intros; apply GlobalTheory.CurveDens.exists_isDens_pos <;> assumption)
