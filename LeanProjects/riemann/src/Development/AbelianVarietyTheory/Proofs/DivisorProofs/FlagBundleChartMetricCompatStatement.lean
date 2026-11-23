import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChartMetricCompat
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
theorem _root_.GlobalTheory.T.flag_bundle_chart_metric_compat : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (d : ℕ) (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) (σ : k →+* ℂ) (E : ι → B.Modules) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (c : AlgChart q σ 1) (cE : ∀ a, Chart (E a) (r a)) (c' : AlgChart p σ (d + 1)), IsCell e π w c c' → (∀ a, IsCellFrame e π w c' a (h a) (fl a) (cE a)) → ∀ y ∈ c'.e.source, (∀ z : Σ a, Fin (r a), chernMat ((VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)).φ σ) c' y = cHess (d + 1) (fun v => (rootWt e (fun a u => ((h a).met σ).G (cE a) (c.e.symm u)) z v : ℂ)) (c'.e y)) ∧ ∀ a, flagMat ((h a).pull π w) (fl a) σ c' y = ∑ i, formMat (extTrace (stepGram e (fun a u => ((h a).met σ).G (cE a) (c.e.symm u)) a i) (c'.e y)) := by
  first | exact @GlobalTheory.MixDens.chern_bc_cell | exact GlobalTheory.MixDens.chern_bc_cell | (intros; apply GlobalTheory.MixDens.chern_bc_cell <;> assumption)
