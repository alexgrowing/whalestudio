import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerExponentialChartLimit
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
theorem _root_.GlobalTheory.T.kaehler_exponential_chart_limit : GlobalTheory.HeightParts.KernelSt → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) (σ : k →+* ℂ) (d : ℕ)
    [SmoothOfRelativeDimension d p] (a : ChartForm p σ d) (E : ChartMap p σ d), IsKaehlerForm (GlobalTheory.AnRead.all p σ d) a →
    IsExph a E → ∀ (f : GlobalTheory.CxPts p σ → ℝ) (c : GlobalTheory.AlgChart p σ d) (y : GlobalTheory.CxPts p σ), y ∈ c.e.source →
    (∃ U ∈ 𝓝 (c.e y), ContinuousOn (f ∘ c.e.symm) U) → Tendsto (fun t => rho a E f y t) (𝓝[>] 0) (𝓝 (f y)) := by
  first | exact @GlobalTheory.RegLim.rho_tendsto | exact GlobalTheory.RegLim.rho_tendsto | (intros; apply GlobalTheory.RegLim.rho_tendsto <;> assumption)
