import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCoeffsTendstoZero
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffs_adic_finite_of_span_eq_univ : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) = ⊤ → ∀ (X : Type) (z : X → M), (∀ n : ℕ, {χ | z χ ∉ (maximalIdeal R ^ n • ⊤ : Submodule R M)}.Finite) → ∃ c : X → Fin r → R, (∀ χ, z χ = ∑ j, c χ j • s j) ∧ ∀ n : ℕ, {χ | ¬ ∀ j, c χ j ∈ maximalIdeal R ^ n}.Finite := by
  first | exact @GlobalTheory.adic_coeffs_tendsto_zero | exact GlobalTheory.adic_coeffs_tendsto_zero | (intros; apply GlobalTheory.adic_coeffs_tendsto_zero <;> assumption)
