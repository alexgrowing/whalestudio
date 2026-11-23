import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialEqOfUpperUnipotentDoubleCoset
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_eq_of_upperUnipotent_double_coset : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (w w' u u' : GG g N), (∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) → (∃ σ : Equiv.Perm (Fin N), ∀ a b, w'.val a b ≠ 0 → a = σ b) → IsUp g N u → IsUp g N u' → u * w = w' * u' → w = w' := by
  first | exact @GlobalTheory.BadShare.monomial_eq_of_unipotent_double_coset | exact GlobalTheory.BadShare.monomial_eq_of_unipotent_double_coset | (intros; apply GlobalTheory.BadShare.monomial_eq_of_unipotent_double_coset <;> assumption)
