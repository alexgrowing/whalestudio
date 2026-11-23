import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLocalRingQuotientPairwiseIsCoprimeIInfEq
import Mathlib
open scoped TensorProduct
open Function
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localRing_quotients_coprime_iInf_eq_bot : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [Module.Finite ℤ_[ℓ] A], ∃ (ι : Type) (_ : Fintype ι) (I : ι → Ideal A), (∀ i, IsLocalRing (A ⧸ I i)) ∧ Pairwise (IsCoprime on I) ∧ ⨅ i, I i = ⊥ := by
  first | (exact @GlobalTheory.exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt) | (exact GlobalTheory.exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt) | (intros; apply GlobalTheory.exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt  <;> assumption)
