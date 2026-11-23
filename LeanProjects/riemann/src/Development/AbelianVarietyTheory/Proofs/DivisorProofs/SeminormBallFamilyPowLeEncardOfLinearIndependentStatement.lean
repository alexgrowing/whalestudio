import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeminormBallFamilyPowLeEncardOfLinearIndependent
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
open Filter Topology
open GlobalTheory GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seminormBallFamily_pow_le_encard_of_linearIndependent : ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (r Q : ℕ) (R : ℝ) (v : Fin r → G), 0 ≤ R → LinearIndependent ℤ v → (∀ j, v j ∈ B R) → ((Q ^ r : ℕ) : ℕ∞) ≤ (B (r * Q * R)).encard := by
  first | exact @GlobalTheory.VolBr.isBallFam_pow_le_encard | exact GlobalTheory.VolBr.isBallFam_pow_le_encard | (intros; apply GlobalTheory.VolBr.isBallFam_pow_le_encard <;> assumption)
