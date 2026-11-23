import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerChartLogMeanBound
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
theorem _root_.GlobalTheory.T.kaehler_chart_log_mean_bound : GlobalTheory.HeightParts.KernelSt → ∀ {k : Type} [CommRing k] {Y : AlgebraicGeometry.Scheme.{0}} {p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k} {σ : k →+* ℂ} {d : ℕ} [SmoothOfRelativeDimension d p] [CompactSpace (GlobalTheory.CxPts p σ)] (a : GlobalTheory.ShFam.ChartForm p σ d) (E : GlobalTheory.ChernReg.ChartMap p σ d) (f : GlobalTheory.CxPts p σ → ℝ), GlobalTheory.ShFam.IsKaehlerForm (GlobalTheory.AnRead.all p σ d) a → GlobalTheory.ChernReg.IsExph a E → (∀ y, Real.exp 1 ≤ f y) → (∀ y₀, ∃ ch : GlobalTheory.AlgChart p σ d, y₀ ∈ ch.e.source ∧ GlobalTheory.LogMean.LogBallBd (f ∘ ch.e.symm) (ch.e y₀) (2 * d)) → ∃ C t₀ : ℝ, 0 < C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ (ch : GlobalTheory.AlgChart p σ d) (y : GlobalTheory.CxPts p σ), y ∈ ch.e.source → MeasureTheory.Integrable (fun ξ => Real.log (f (E ch y (t • ξ))) * GlobalTheory.ChernReg.cutoff (a ch y ξ)) ∧ GlobalTheory.ChernReg.rhoIn a E (fun z => Real.log (f z)) ch y t ≤ Real.log (C * Real.log (1 / t)) := by
  first | exact @GlobalTheory.LogMean.rhoIn_log_le_log_log | exact GlobalTheory.LogMean.rhoIn_log_le_log_log | (intros; apply GlobalTheory.LogMean.rhoIn_log_le_log_log <;> assumption)
