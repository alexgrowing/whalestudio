import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartSmooth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_chart_smooth : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (c : AlgChart p σ D), SmoothOfRelativeDimension D (c.U.ι ≫ p) := by
  first | exact @GlobalTheory.ChartSmooth.smooth_chart | exact GlobalTheory.ChartSmooth.smooth_chart | (intros; apply GlobalTheory.ChartSmooth.smooth_chart <;> assumption)
