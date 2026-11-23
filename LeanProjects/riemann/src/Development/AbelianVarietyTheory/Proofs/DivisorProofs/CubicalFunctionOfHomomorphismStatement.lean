import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalFunctionOfHomomorphism
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_function_of_homomorphism : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (A : Type) [CommGroup A] (h : X → A), (∀ a b, h (a + b) = h a * h b) → ∃ k : X → A, (∀ a a' b : X, k (a + a' + b) * k a * k a' * k b = k (a + a') * k (a + b) * k (a' + b)) ∧ ∀ a, k (-a) = h a * k a := by
  first | exact @GlobalTheory.hom_eq_evenness_defect_of_cube | exact GlobalTheory.hom_eq_evenness_defect_of_cube | (intros; apply GlobalTheory.hom_eq_evenness_defect_of_cube <;> assumption)
