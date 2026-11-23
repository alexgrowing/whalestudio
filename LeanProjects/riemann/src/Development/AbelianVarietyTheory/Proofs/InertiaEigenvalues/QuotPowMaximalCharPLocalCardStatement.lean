import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalCharPLocalCard
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_pow_finite_uniformizer_card_eq : ∀ (L : Type) [Field L] [NumberField L] (la J : Ideal (𝓞 L)) [la.IsMaximal] (l e b : ℕ), l.Prime → 0 < e → 0 < b → la ⊔ J = ⊤ → Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e * J → CharP (𝓞 L ⧸ la ^ (e * b)) (l ^ b) ∧ Finite (𝓞 L ⧸ la ^ (e * b)) ∧ ∃ π : 𝓞 L ⧸ la ^ (e * b), (∀ x : 𝓞 L ⧸ la ^ (e * b), ¬ IsUnit x ↔ π ∣ x) ∧ Ideal.span {((l : ℕ) : 𝓞 L ⧸ la ^ (e * b))} = Ideal.span {π ^ e} ∧ Nat.card (𝓞 L ⧸ la ^ (e * b)) = Nat.card ((𝓞 L ⧸ la ^ (e * b)) ⧸ Ideal.span {π}) ^ (b * e) := by
  first | exact @GlobalTheory.quot_pow_maximal_charP_local_card | exact GlobalTheory.quot_pow_maximal_charP_local_card | (intros; apply GlobalTheory.quot_pow_maximal_charP_local_card <;> assumption)
