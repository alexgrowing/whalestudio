import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBallBoundLocalChart
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
theorem _root_.GlobalTheory.T.log_ball_bound_local_chart : ∀ {d : ℕ} (U : Set (ReciprocityTheory.L2DbarEstimates.V d)) (v₀ : ReciprocityTheory.L2DbarEstimates.V d) (Φ : ReciprocityTheory.L2DbarEstimates.V d → (Fin d → ℂ)) (H f : ReciprocityTheory.L2DbarEstimates.V d → ℝ) (I : Finset (Fin d)), IsOpen U → v₀ ∈ U → ContDiffOn ℝ 1 Φ U → Function.Bijective (fderiv ℝ Φ v₀) → ContinuousOn H U → (∀ v, 0 ≤ f v) → (∀ v ∈ U, (∀ i ∈ I, Φ v i ≠ 0) → f v = H v - ∑ i ∈ I, Real.log (‖Φ v i‖ ^ 2)) → GlobalTheory.LogMean.LogBallBd f v₀ (2 * d) := by
  first | exact @GlobalTheory.LogModel.main | exact GlobalTheory.LogModel.main | (intros; apply GlobalTheory.LogModel.main <;> assumption)
