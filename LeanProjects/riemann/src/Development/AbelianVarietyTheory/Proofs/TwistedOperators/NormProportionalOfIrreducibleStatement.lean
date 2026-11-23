import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormProportionalOfIrreducible
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_eq_mul_of_finrank_hwSub_eq_one : ∀ (p q : ℕ) (M : GKMod p q) (Λ : Ix p q → ℚ) (H₁ H₂ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (E₁ : M.V →ₗ[ℂ] H₁) (E₂ : M.V →ₗ[ℂ] H₂), IrrGK M → Module.finrank ℂ ↥(hwSub M.act Λ) = 1 → Function.Injective E₁ → (∀ Z x y, inner ℂ (E₁ (M.act Z x)) (E₁ y) = inner ℂ (E₁ x) (E₁ (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (E₂ (M.act Z x)) (E₂ y) = inner ℂ (E₂ x) (E₂ (M.act (adjZ Z) y))) → ∃ c : ℝ, ∀ y, ‖E₂ y‖ = c * ‖E₁ y‖ := by
  first | exact @GlobalTheory.FockTensor.norm_proportional_of_irreducible | exact GlobalTheory.FockTensor.norm_proportional_of_irreducible | (intros; apply GlobalTheory.FockTensor.norm_proportional_of_irreducible <;> assumption)
