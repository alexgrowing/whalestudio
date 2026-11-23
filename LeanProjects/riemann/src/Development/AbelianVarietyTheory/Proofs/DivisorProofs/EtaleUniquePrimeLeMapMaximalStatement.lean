import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleUniquePrimeLeMapMaximal
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_unique_prime_le_map_maximal : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] [Algebra.Etale B A] (P : Ideal B), P.IsMaximal → ∀ (Q : Ideal A), (∀ Q' : Ideal A, Q'.IsPrime → P.map (algebraMap B A) ≤ Q' → Q' = Q) → Q ≤ P.map (algebraMap B A) := by
  first | (exact @GlobalTheory.etale_prime_le_map_of_unique) | (exact GlobalTheory.etale_prime_le_map_of_unique) | (intros; apply GlobalTheory.etale_prime_le_map_of_unique <;> assumption)
