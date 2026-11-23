import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogIdealMulSpanMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_coordinates_p_power_denominator : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : ℝ), ∃ e : ℕ, ∀ c : G.C, (∀ (w : Fin G.m) (a b : Fin G.n), ‖((G.rho w c a b : G.Fw w) : PadicAlgCl p)‖ ≤ B ∧ ‖((G.rho w (sh G c) a b : G.Fw w) : PadicAlgCl p)‖ ≤ B) → ∀ i, ∃ (k : ℤ) (m : ℕ), ¬ p ∣ m ∧ (Module.finBasis ℚ G.C).repr c i * (p : ℚ) ^ e = k / m := by
  first | (exact @GlobalTheory.CoordP.coord_bound) | (exact GlobalTheory.CoordP.coord_bound) | (intros; apply GlobalTheory.CoordP.coord_bound <;> assumption)
