import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallLePowMulSmaller
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
open Filter Topology
open GlobalTheory GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_seminormBall_le_pow_mul_smaller : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (R : ℝ) (q r : ℕ), 0 < q → (∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ B R) → n ≤ r) → (B R).encard ≤ ((q ^ r : ℕ) : ℕ∞) * (B (2 * R / q)).encard := by
  first | exact @GlobalTheory.VolBr.encard_ball_le_pow_mul | exact GlobalTheory.VolBr.encard_ball_le_pow_mul | (intros; apply GlobalTheory.VolBr.encard_ball_le_pow_mul <;> assumption)
