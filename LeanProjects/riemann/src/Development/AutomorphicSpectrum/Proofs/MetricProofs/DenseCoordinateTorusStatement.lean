import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DenseCoordinateTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_coordinate_torus : ∀ n : ℕ, Dense {z : Fin n → ℂ | ∀ i, z i ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero <;> assumption)
