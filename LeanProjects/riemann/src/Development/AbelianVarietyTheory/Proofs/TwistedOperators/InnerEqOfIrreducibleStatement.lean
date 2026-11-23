import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqOfIrreducible
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_eq_of_irrGK_of_inner_hw_eq : ∀ (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (j₁ : M.V →ₗ[ℂ] H₁) (j₂ : M.V →ₗ[ℂ] H₂), (∀ Z x y, inner ℂ (j₁ (M.act Z x)) (j₁ y) = inner ℂ (j₁ x) (j₁ (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (j₂ (M.act Z x)) (j₂ y) = inner ℂ (j₂ x) (j₂ (M.act (adjZ Z) y))) → Function.Injective j₂ → IrrGK M → ∀ (μ : Ix p q → ℚ) (v : M.V), IsHW M.act μ v → Module.finrank ℂ ↥(hwSub M.act μ) = 1 → inner ℂ (j₁ v) (j₁ v) = inner ℂ (j₂ v) (j₂ v) → ∀ x y, inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y) := by
  first | exact @GlobalTheory.InvFormUnique.inner_eq_of_irreducible | exact GlobalTheory.InvFormUnique.inner_eq_of_irreducible | (intros; apply GlobalTheory.InvFormUnique.inner_eq_of_irreducible <;> assumption)
