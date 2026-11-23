import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChartMetricBlockForm
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_chart_metric_block_form : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (f : Y ⟶ B) (w : f ≫ q = p) (σ : k →+* ℂ) (D d : ℕ) (c : AlgChart p σ D) (c' : AlgChart q σ d) (y : CxPts p σ), y ∈ c.e.source → PtsOver.map f w (spMap σ) y ∈ c'.e.source → ∃ (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ), ∀ (A : HermLB q) (i : (A.pull f w).B.ι), y ∈ ptsIn p σ ((A.pull f w).B.U i) → ∃ K : Matrix (Fin d) (Fin d) ℂ, c.hess ((A.pull f w).φ σ) i y = P * K * Q := by
  first | exact @GlobalTheory.HessPull.hess_pull_factor | exact GlobalTheory.HessPull.hess_pull_factor | (intros; apply GlobalTheory.HessPull.hess_pull_factor <;> assumption)
