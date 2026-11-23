import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChartLift
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
theorem _root_.GlobalTheory.T.flag_bundle_chart_lift : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (d : ℕ) (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) (σ : k →+* ℂ) (E : ι → B.Modules) (h : ∀ a, VMetric q (E a) (r a)) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ (c₀ : AlgChart q σ 1), ∀ y ∈ c₀.e.source, ∃ (c : AlgChart q σ 1) (cE : ∀ a, Chart (E a) (r a)) (c' : AlgChart p σ (d + 1)), y ∈ c.e.source ∧ (∀ a, c.e.source ⊆ ptsIn q σ (cE a).U) ∧ IsCell e π w c c' ∧ ∀ a, IsCellFrame e π w c' a (h a) (fl a) (cE a) := by
  first | exact @GlobalTheory.MixDens.exists_cell_charts | exact GlobalTheory.MixDens.exists_cell_charts | (intros; apply GlobalTheory.MixDens.exists_cell_charts <;> assumption)
