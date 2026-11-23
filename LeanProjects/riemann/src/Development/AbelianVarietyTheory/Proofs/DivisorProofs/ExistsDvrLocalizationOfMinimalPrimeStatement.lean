import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrLocalizationOfMinimalPrime
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_localization_of_minimal_prime' : ∀ {κ : Type} [Field κ] (R : Subring κ) [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R κ] (Q : Ideal R) [Q.IsPrime], Q ≠ ⊥ → (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ Q → p = Q) → ∃ W : ValuationSubring κ, IsDiscreteValuationRing W ∧ (∀ r : R, (r : κ) ∈ W) ∧ (∀ r : R, r ∉ Q → (r : κ)⁻¹ ∈ W) ∧ (∀ r : R, r ∈ Q → r ≠ 0 → (r : κ)⁻¹ ∉ W) ∧ (∀ w ∈ W, ∃ b s : R, s ∉ Q ∧ w = b / s) := by
  first | exact @GlobalTheory.exists_dvr_localization_of_minimal_prime | exact GlobalTheory.exists_dvr_localization_of_minimal_prime | (intros; apply GlobalTheory.exists_dvr_localization_of_minimal_prime <;> assumption)
