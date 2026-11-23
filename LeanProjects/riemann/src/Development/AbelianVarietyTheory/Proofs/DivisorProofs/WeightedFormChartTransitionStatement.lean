import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFormChartTransition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_form_chart_transition : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ (α : AlgChart p σ (d + 1) → CxPts p σ → Fin (d + 1) → ℂ), (∀ c : AlgChart p σ (d + 1), ∀ y ∈ c.e.source, ∀ j, ContDiffAt ℝ 1 (fun v => α c (c.e.symm v) j) (c.e y)) → (∀ (c c' : AlgChart p σ (d + 1)) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → ∀ j, α c y j = ∑ a, transMat c c' y a j * α c' y a) → ∀ (c₀ : AlgChart p σ (d + 1)) (K : Set (CxPts p σ)), IsCompact K → K ⊆ c₀.e.source → (∀ c : AlgChart p σ (d + 1), ∀ y ∈ c.e.source, y ∉ K → ∀ j, α c y j = 0) → total (fun (c : AlgChart p σ (d + 1)) y => mix d (chernMat φ c y) (Matrix.of fun j l => dbar (fun v => α c (c.e.symm v) j) (c.e y) (EuclideanSpace.single l 1))) = 0 := by
  first | exact @GlobalTheory.MixDens.total_dbar_eq_zero_of_compact_chart | exact GlobalTheory.MixDens.total_dbar_eq_zero_of_compact_chart | (intros; apply GlobalTheory.MixDens.total_dbar_eq_zero_of_compact_chart <;> assumption)
