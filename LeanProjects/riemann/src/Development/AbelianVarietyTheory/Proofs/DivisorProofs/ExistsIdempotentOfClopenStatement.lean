import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_of_clopen : ∀ (X : Scheme.{0}) (U : Set X), IsClopen U → ∃ e : Γ(X, ⊤), e * e = e ∧ ((X.basicOpen e : X.Opens) : Set X) = U := by
  first | exact @GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen | exact GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen | (intros; apply GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen <;> assumption)
