import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardCosetRepsEqRelIndex
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_coset_reps_eq_relIndex : ∀ (X : Type) [AddCommGroup X] (A L : AddSubgroup X) (T : Finset X), L ≤ A → (∀ t ∈ T, t ∈ A) → (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) → T.card = L.relIndex A := by
  first | exact @GlobalTheory.CompanionTheory.Transversal.card_eq_relIndex | exact GlobalTheory.CompanionTheory.Transversal.card_eq_relIndex | (intros; apply GlobalTheory.CompanionTheory.Transversal.card_eq_relIndex <;> assumption)
