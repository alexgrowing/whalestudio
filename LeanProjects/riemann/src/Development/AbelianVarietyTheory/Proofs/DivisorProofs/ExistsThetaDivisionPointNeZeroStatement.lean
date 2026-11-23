import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDivisionPointNeZero
import Mathlib
open Complex Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_division_point_ne_zero : ∀ (g N : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (β : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → 2 ≤ N → (∀ j, β j ≠ 0) → Differentiable ℂ f → f ≠ 0 → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) = β j * cexp (-(2 * Real.pi * I) * N * z j) * f z) → ∃ m n : Fin g → ℤ, f ((N : ℂ)⁻¹ • ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) ≠ 0 := by
  first | exact @GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero | exact GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero | (intros; apply GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero <;> assumption)
