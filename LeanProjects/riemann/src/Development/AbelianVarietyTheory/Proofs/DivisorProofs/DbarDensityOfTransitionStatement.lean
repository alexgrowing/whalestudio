import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarDensityOfTransition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_density_of_transition : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (m : AlgChart p σ 1 → CxPts p σ → ℂ), (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) → (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) → IsDens (fun (c : AlgChart p σ 1) (y : CxPts p σ) => (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re) := by
  first | exact @GlobalTheory.CurveDens.isDens_re_dbar_coeff | exact GlobalTheory.CurveDens.isDens_re_dbar_coeff | (intros; apply GlobalTheory.CurveDens.isDens_re_dbar_coeff <;> assumption)
