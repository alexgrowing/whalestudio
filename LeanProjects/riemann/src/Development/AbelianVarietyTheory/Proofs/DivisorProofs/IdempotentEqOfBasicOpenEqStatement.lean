import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEqOfBasicOpenEq
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_eq_of_basicOpen_eq' : ∀ (X : Scheme.{0}) (e e' : Γ(X, ⊤)), e * e = e → e' * e' = e' → X.basicOpen e = X.basicOpen e' → e = e' := by
  first | exact @GlobalTheory.idempotent_eq_of_basicOpen_eq | exact GlobalTheory.idempotent_eq_of_basicOpen_eq | (intros; apply GlobalTheory.idempotent_eq_of_basicOpen_eq <;> assumption)
