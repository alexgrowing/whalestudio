import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DdcLogNormBoundedByKaehler
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_log_norm_bounded_by_kaehler : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d p] (σ : k →+* ℂ) (C : Closeds Y) (n : CxPts p σ → ℝ) (a : ChartForm p σ d), IsProjOver p → IsDivNorm (AnRead.all p σ d) C n → IsKaehlerForm (AnRead.all p σ d) a → ∃ K : ℝ, ∀ (c : AlgChart p σ d), ∀ y ∈ c.e.source, ¬ LiesIn y C → ∀ ξ, |ddcForm (fun z => Real.exp 1 - Real.log (n z ^ 2)) c y ξ| ≤ K * a c y ξ := by
  first | exact @GlobalTheory.ShFam.CurvBound.exists_bound | exact GlobalTheory.ShFam.CurvBound.exists_bound | (intros; apply GlobalTheory.ShFam.CurvBound.exists_bound <;> assumption)
