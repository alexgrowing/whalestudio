import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleIncomparability
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ind_etale_prime_comparison : ∀ (B O : Type) [CommRing B] [CommRing O] [Algebra B O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra B O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra B E) (_ : Algebra.Etale B E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[B] Si i)) → ∀ p p' : Ideal O, p.IsPrime → p'.IsPrime → p ≤ p' → p.comap (algebraMap B O) = p'.comap (algebraMap B O) → p = p' := by
  first | (exact @GlobalTheory.eq_of_le_of_comap_eq_of_indEtale) | (exact GlobalTheory.eq_of_le_of_comap_eq_of_indEtale) | (intros; apply GlobalTheory.eq_of_le_of_comap_eq_of_indEtale  <;> assumption)
