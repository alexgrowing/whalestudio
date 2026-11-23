import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBallFiniteChartCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBallBd
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry MeasureTheory GlobalTheory.ChernReg GlobalTheory.ShFam GlobalTheory.CxPts Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_ball_finite_chart_cover : ∀ {k : Type} [CommRing k] {Y : AlgebraicGeometry.Scheme.{0}} {p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k} {σ : k →+* ℂ} {d : ℕ} [CompactSpace (GlobalTheory.CxPts p σ)] (f : GlobalTheory.CxPts p σ → ℝ), (∀ y₀, ∃ ch : GlobalTheory.AlgChart p σ d, y₀ ∈ ch.e.source ∧ GlobalTheory.LogMean.LogBallBd (f ∘ ch.e.symm) (ch.e y₀) (2 * d)) → ∃ (n : ℕ) (ch : Fin n → GlobalTheory.AlgChart p σ d) (K : Fin n → Set (ReciprocityTheory.L2DbarEstimates.V d)) (C ρ₀ : ℝ), 0 ≤ C ∧ 0 < ρ₀ ∧ (∀ j, IsCompact (K j) ∧ K j ⊆ (ch j).e.target) ∧ (∀ y, ∃ j, y ∈ (ch j).e.source ∧ (ch j).e y ∈ K j) ∧ ∀ j, ∀ v ∈ K j, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → MeasureTheory.IntegrableOn (f ∘ (ch j).e.symm) (Metric.ball v ρ) ∧ ∫ w in Metric.ball v ρ, f ((ch j).e.symm w) ≤ C * ρ ^ (2 * d) * (1 + Real.log (1 / ρ)) := by
  first | exact @GlobalTheory.LogMean.exists_finite_chart_cover_logBallBd | exact GlobalTheory.LogMean.exists_finite_chart_cover_logBallBd | (intros; apply GlobalTheory.LogMean.exists_finite_chart_cover_logBallBd <;> assumption)
