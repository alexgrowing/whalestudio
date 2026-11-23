import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartCompactCoverBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry CategoryTheory MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates GlobalTheory GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_compact_cover_bounds : ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P →
    ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ), ∃ (n : ℕ) (ch : Fin n → AlgChart (O.var c).str σ (O.var c).dim)
      (K : Fin n → Set (V (O.var c).dim)) (κ B : ℝ), 0 < κ ∧ 0 ≤ B ∧
      (∀ j, IsCompact (K j) ∧ K j ⊆ (ch j).e.target) ∧ (∀ y, ∃ j, y ∈ (ch j).e.source ∧ (ch j).e y ∈ K j) ∧
      ∀ j, ∀ y ∈ (ch j).e.source, (ch j).e y ∈ K j → y ∈ offBd O.Φ c σ →
        ∀ w ∈ Metric.ball ((ch j).e y) (κ * Real.exp (-(O.met.r c σ y / 2))), w ∈ (ch j).e.target ∧
          (ch j).e.symm w ∈ offBd O.Φ c σ ∧ O.met.r c σ ((ch j).e.symm w) ≤ O.met.r c σ y + B ∧
          ∀ ξ : V (O.var c).dim, P.om c σ (ch j) ((ch j).e.symm w) ξ.ofLp ≤ B * ‖ξ‖ ^ 2 := by
  first | exact @GlobalTheory.CoverCharts.exists_charts_margin | exact GlobalTheory.CoverCharts.exists_charts_margin | (intros; apply GlobalTheory.CoverCharts.exists_charts_margin <;> assumption)
