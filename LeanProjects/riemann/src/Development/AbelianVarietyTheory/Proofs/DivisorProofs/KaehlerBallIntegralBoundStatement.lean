import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerBallIntegralBound
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
theorem _root_.GlobalTheory.T.rho_sub_self_le_of_fderiv_le : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    (a : ChartForm p σ d) (E : ChartMap p σ d) (c : AlgChart p σ d) (f : CxPts p σ → ℝ) (y : CxPts p σ) (t Cc M : ℝ),
    IsKaehlerForm (AnRead.all p σ d) a → IsExph a E → y ∈ c.e.source → 0 < t → 0 < Cc → 0 ≤ M →
    Metric.ball (c.e y) (Cc * t) ⊆ c.e.target →
    (∀ g : CxPts p σ → ℝ, IntegrableOn (g ∘ c.e.symm) (Metric.ball (c.e y) (Cc * t)) →
      Integrable (fun ξ => g (E c y (t • ξ)) * ChernReg.cutoff (a c y ξ)) ∧
      |rho a E g y t| ≤ Cc / t ^ (2 * d) * ∫ v in Metric.ball (c.e y) (Cc * t), |g (c.e.symm v)|) →
    (∀ w ∈ Metric.ball (c.e y) (Cc * t), DifferentiableAt ℝ (f ∘ c.e.symm) w ∧ ‖fderiv ℝ (f ∘ c.e.symm) w‖ ≤ M) →
    rho a E f y t - f y ≤ Cc * (volume (Metric.ball (0 : V d) 1)).toReal * Cc ^ (2 * d) * Cc * M * t := by
  first | exact @GlobalTheory.AvgMV.avg_sub_le | exact GlobalTheory.AvgMV.avg_sub_le | (intros; apply GlobalTheory.AvgMV.avg_sub_le <;> assumption)
