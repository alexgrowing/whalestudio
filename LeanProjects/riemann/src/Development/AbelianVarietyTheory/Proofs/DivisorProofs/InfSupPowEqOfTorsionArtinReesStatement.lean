import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfSupPowEqOfTorsionArtinRees
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inf_sup_pow_eq_of_torsion_artinRees : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (K τ τ' : Ideal B), τ ≤ τ' → (∀ b ∈ τ', ∀ f ∈ K, ∃ m : ℕ, f ^ m * b ∈ τ) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → τ' ⊓ (τ ⊔ K ^ k) = τ := by
  first | exact @GlobalTheory.inf_sup_pow_eq_of_torsion | exact GlobalTheory.inf_sup_pow_eq_of_torsion | (intros; apply GlobalTheory.inf_sup_pow_eq_of_torsion <;> assumption)
