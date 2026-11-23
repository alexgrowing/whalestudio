import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChartBigCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChartLift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_chart_big_cell : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (n D : ℕ) (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a))) (σ : k →+* ℂ) (E : ι → B.Modules) (h : ∀ a, VMetric q (E a) (r a)) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ (c₀ : AlgChart q σ n), ∀ y ∈ c₀.e.source, ∃ (c : AlgChart q σ n) (cE : ∀ a, Chart (E a) (r a)) (c' : AlgChart p σ D), y ∈ c.e.source ∧ (∀ a, c.e.source ⊆ ptsIn q σ (cE a).U) ∧ BigCell.IsCell ε π w c c' ∧ ∀ a, BigCell.IsCellFrame ε π w c' a (h a) (fl a) (cE a) := by
  first | exact @GlobalTheory.BigCell.exists_cell_charts | exact GlobalTheory.BigCell.exists_cell_charts | (intros; apply GlobalTheory.BigCell.exists_cell_charts <;> assumption)
