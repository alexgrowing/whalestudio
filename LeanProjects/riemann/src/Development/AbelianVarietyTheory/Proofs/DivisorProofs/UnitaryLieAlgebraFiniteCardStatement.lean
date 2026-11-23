import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieAlgebraFiniteCard
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix GlobalTheory.SUCong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lie_algebra_finite_card : ∀ {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (τ : R →+* R) (k : Subring R) (w : R) (Hb H' : Matrix n n R) (q : ℕ), (∀ x ∈ k, τ x = x) → w + τ w = 1 → IsUnit (w - τ w) → (∀ x : R, ∃ a ∈ k, ∃ b ∈ k, x = a + b * w) → (∀ x ∈ k, x ≠ 0 → ∃ y ∈ k, x * y = 1) → Nat.card k = q → Formalism.UG.cT τ Hb = Hb → Hb * H' = 1 → Nat.card {Y : Matrix n n R // Formalism.UG.cT τ Y * Hb + Hb * Y = 0 ∧ Y.trace = 0} = q ^ (Fintype.card n ^ 2 - 1) := by
  first | exact @GlobalTheory.SkewCount.card_skew_traceless | exact GlobalTheory.SkewCount.card_skew_traceless | (intros; apply GlobalTheory.SkewCount.card_skew_traceless <;> assumption)
