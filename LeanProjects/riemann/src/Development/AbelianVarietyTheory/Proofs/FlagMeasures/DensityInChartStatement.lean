import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DensityInChart
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_measure_image_ball_div_volume : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)) (c : ℝ≥0∞), PI.IsMatGroup S → PI.IsHaarOnM S μ → HasDens S μ c → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → Matrix (Fin m) (Fin m) ℂ) (L : E ≃L[ℝ] lieE S), Φ 0 = 1 → (∀ᶠ x in 𝓝 (0 : E), Φ x ∈ S) → (∀ i j, ∃ D : E →L[ℝ] ℂ, HasStrictFDerivAt (fun x => Φ x i j) D 0 ∧ ∀ v, D v = unrealify ((L v : lieE S) : EuclideanSpace ℝ _) i j) → Tendsto (fun ρ : ℝ => μ ((fun x => Matrix.of.symm (Φ x)) '' Metric.ball 0 ρ) / volume (L '' Metric.ball (0 : E) ρ)) (𝓝[>] 0) (𝓝 c) := by
  first | exact @GlobalTheory.ChartDensity.density_in_chart | exact GlobalTheory.ChartDensity.density_in_chart | (intros; apply GlobalTheory.ChartDensity.density_in_chart <;> assumption)
