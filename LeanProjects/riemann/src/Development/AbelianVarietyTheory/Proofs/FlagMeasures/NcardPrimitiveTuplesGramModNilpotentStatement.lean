import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimitiveTuplesGramModNilpotent
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_primitive_tuples_gram_mod_nilpotent : ∀ {A B : Type} [CommRing A] [Finite A] [CommRing B] (c : A →+* A) (c' : B →+* B), (∀ u, c (c u) = u) → ∀ (p : A), IsNilpotent p → ∀ (φ : A →+* B), Function.Surjective φ → (∀ u, φ (c u) = c' (φ u)) → (∀ u, φ u = 0 ↔ p ∣ u) → ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) A), Set.ncard {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} = Nat.card {u : A // p ∣ u} ^ (n * m) * Set.ncard (sols c' n (G.map φ)) := by
  first | exact @GlobalTheory.GramCount.ncard_gram_mod_eq_card_ker_pow_mul | exact GlobalTheory.GramCount.ncard_gram_mod_eq_card_ker_pow_mul | (intros; apply GlobalTheory.GramCount.ncard_gram_mod_eq_card_ker_pow_mul <;> assumption)
