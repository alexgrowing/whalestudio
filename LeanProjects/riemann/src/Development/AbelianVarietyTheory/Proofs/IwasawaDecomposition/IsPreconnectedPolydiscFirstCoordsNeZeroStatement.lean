import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPreconnectedPolydiscFirstCoordsNeZero
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPreconnected_ball_inter_coords_ne_zero : ∀ (n a : ℕ) (ha : a ≤ n), _root_.IsPreconnected {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} := by
  first | exact @GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero | exact GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero | (intros; apply GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero <;> assumption)
