import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeasureCongruenceInvariant
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_measure_congruence_invariant : ∀ (n : ℕ) (g : Mat n), g.det ≠ 0 → ∀ T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ), (∀ v, hOf (T v) = g * hOf v * gᴴ) → LinearMap.det T = ‖g.det‖ ^ (2 * n) → Measure.map T (coneMeas n) = coneMeas n := by
  first | exact @GlobalTheory.CompanionTheory.ConeHaar.map_coneMeas_eq | exact GlobalTheory.CompanionTheory.ConeHaar.map_coneMeas_eq | (intros; apply GlobalTheory.CompanionTheory.ConeHaar.map_coneMeas_eq <;> assumption)
