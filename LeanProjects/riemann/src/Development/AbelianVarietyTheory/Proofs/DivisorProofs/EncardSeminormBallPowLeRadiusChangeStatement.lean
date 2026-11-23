import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallPowLeRadiusChange
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
open Filter Topology GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_seminormBall_pow_le_radius_change : ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (R : ℝ) (Q e : ℕ), 1 ≤ R → 2 * R + 1 ≤ Q → (B R).Finite → (B R).encard ^ e ≤ (B 1).encard ^ e * (B (R * Q ^ e)).encard := by
  first | exact @GlobalTheory.VolBr.encard_ball_pow_le | exact GlobalTheory.VolBr.encard_ball_pow_le | (intros; apply GlobalTheory.VolBr.encard_ball_pow_le <;> assumption)
