import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallMulLeConvexity
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
open Filter Topology GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_seminormBall_mul_le_convexity : ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ n : ℕ, 0 < n → (B n).Finite → (B n).encard * (B (n / 2)).encard ≤ (B 1).encard * (B (n ^ 2 + n / 2)).encard := by
  first | exact @GlobalTheory.VolBr.isBallFam_encard_mul_le | exact GlobalTheory.VolBr.isBallFam_encard_mul_le | (intros; apply GlobalTheory.VolBr.isBallFam_encard_mul_le <;> assumption)
