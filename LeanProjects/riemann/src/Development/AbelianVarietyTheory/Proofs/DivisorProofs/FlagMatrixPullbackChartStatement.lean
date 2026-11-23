import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixPullbackChart
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
theorem _root_.GlobalTheory.T.flag_matrix_pullback_chart : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (d : ℕ) (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) (σ : k →+* ℂ) (E : B.Modules) (s : ℕ) (h : VMetric q E s), h.IsCInf → ∀ (m : Vert.Flag E s) (c : AlgChart q σ 1) (c' : AlgChart p σ (d + 1)), IsCell e π w c c' → ∀ y ∈ c'.e.source, flagMat (h.pull π w) (m.pull π) σ c' y = ((Real.pi * ∑ i, ((h.stepMet m i).met σ).bcDens (VMetric.stepSeq_shortExact m i) (m.isVB i.castSucc) (m.isVB_gr i) c (PtsOver.map π w (spMap σ) y) : ℝ) : ℂ) • diagonal fun j => (baseDiag (e j) : ℂ) := by
  first | exact @GlobalTheory.MixDens.flagMat_pull_cell | exact GlobalTheory.MixDens.flagMat_pull_cell | (intros; apply GlobalTheory.MixDens.flagMat_pull_cell <;> assumption)
