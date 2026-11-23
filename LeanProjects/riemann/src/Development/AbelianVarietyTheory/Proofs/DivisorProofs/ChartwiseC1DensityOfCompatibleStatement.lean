import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartwiseC1DensityOfCompatible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartwise_C1_density_of_compatible : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (m : AlgChart p σ 1 → CxPts p σ → ℂ), (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) → (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) → total (fun (c : AlgChart p σ 1) (y : CxPts p σ) => (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re) = 0 := by
  first | exact @GlobalTheory.stokes_curve | exact GlobalTheory.stokes_curve | (intros; apply GlobalTheory.stokes_curve <;> assumption)
