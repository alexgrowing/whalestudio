import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotientEqOfPowSubSelfMem
import Mathlib
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_quotient_eq_of_pow_sub_self_mem' : ∀ {R : Type} [CommRing R] (P : Ideal R) [P.IsMaximal] (q : ℕ) (ζ : R), 2 ≤ q → ζ ^ (q - 1) = 1 →
    (∀ j : ℕ, 0 < j → j < q - 1 → ζ ^ j - 1 ∉ P) → (∀ y : R, y ^ q - y ∈ P) → Nat.card (R ⧸ P) = q := by
  first | exact @GlobalTheory.card_quotient_eq_of_pow_sub_self_mem | exact GlobalTheory.card_quotient_eq_of_pow_sub_self_mem | (intros; apply GlobalTheory.card_quotient_eq_of_pow_sub_self_mem <;> assumption)
