import Mathlib

theorem UpperTheory.Reformulated.B.Re1.lower_iff :
    ∀ {n : ℕ} (P : Fin n → Prop) [inst : DecidablePred P],
    (∀ (a b : Fin n), a ≤ b → P b → P a) → ∀ (b : Fin n), P b ↔ (↑b : ℕ) < (Finset.filter P Finset.univ).card := by
  intro n P _ h b
  exact (Fin.lt_card_filter_univ_iff_apply_of_imp P (fun i j hij => h j i hij)).symm
