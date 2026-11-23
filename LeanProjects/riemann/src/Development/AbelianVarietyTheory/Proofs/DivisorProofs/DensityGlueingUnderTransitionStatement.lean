import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityGlueingUnderTransition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.total_re_dbar_eq_zero_of_compact_support_in_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (m : AlgChart p σ 1 → CxPts p σ → ℂ), (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) → (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) → ∀ (c₀ : AlgChart p σ 1) (K : Set (CxPts p σ)), IsCompact K → K ⊆ c₀.e.source → (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∉ K → m c y = 0) → total (fun (c : AlgChart p σ 1) (y : CxPts p σ) => (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re) = 0 := by
  first | exact @GlobalTheory.CurveDens.total_dbar_eq_zero_of_compact_chart | exact GlobalTheory.CurveDens.total_dbar_eq_zero_of_compact_chart | (intros; apply GlobalTheory.CurveDens.total_dbar_eq_zero_of_compact_chart <;> assumption)
