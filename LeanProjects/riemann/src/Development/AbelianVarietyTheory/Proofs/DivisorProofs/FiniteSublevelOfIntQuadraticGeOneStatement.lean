import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSublevelOfIntQuadraticGeOne
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_sublevel_of_int_quadratic_ge_one : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (q : X → ℤ), (∀ a, q (-a) = q a) → (∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b)) → (∀ a, a ≠ 0 → 1 ≤ q a) → ∀ N : ℤ, {a | q a ≤ N}.Finite := by
  first | exact @GlobalTheory.posquad_finite | exact GlobalTheory.posquad_finite | (intros; apply GlobalTheory.posquad_finite <;> assumption)
