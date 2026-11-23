import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHermitianDiagonalizationUnits
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotent_approximation_surjective : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (I : Ideal B) (K : Ideal A) (N : ℕ), (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ I.map (algebraMap B A) ⊔ K) → (I ^ N).map (algebraMap B A) ≤ K → ∀ a : A, ∃ b : B, a - algebraMap B A b ∈ K := by
  first | (exact @GlobalTheory.surj_mod_of_surj_mod_map_sup_of_pow_map_le) | (exact GlobalTheory.surj_mod_of_surj_mod_map_sup_of_pow_map_le) | (intros; apply GlobalTheory.surj_mod_of_surj_mod_map_sup_of_pow_map_le <;> assumption)
