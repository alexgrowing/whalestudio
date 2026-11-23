import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetAntitoneEnumeration

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiset_antitone_enumeration : ∀ {α : Type*} (m : Multiset α) (f : α → ℝ) (P : α → α → Prop), (∀ a b, P a b → f a < f b) → ∃ (h : ℕ) (Δ : Fin h → α), Finset.univ.val.map Δ = m ∧ Antitone (f ∘ Δ) ∧ ∀ i j, i < j → ¬ P (Δ i) (Δ j) := by
  first | exact @GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing | exact GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing | (intros; apply GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing <;> assumption)
