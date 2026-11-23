import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FinrankAddTwoMulOfHyperbolicPairs
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_and_finrank_add_two_mul_of_hyperbolic : ∀ (E V : Type) [Field E] [StarRing E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E), h.IsSymm → ∀ (W : Submodule E V) (i : ℕ) (e f : Fin i → V), (∀ a b, h (e a) (e b) = 0) → (∀ a b, h (f a) (f b) = 0) → (∀ a b, h (f a) (e b) = if a = b then 1 else 0) → (∀ a, ∀ x ∈ W, h x (e a) = 0 ∧ h x (f a) = 0) → W ⊔ Submodule.span E (Set.range e ∪ Set.range f) = ⊤ → LinearIndependent E e ∧ Module.finrank E W + 2 * i = Module.finrank E V := by
  first | exact @GlobalTheory.finrank_add_two_mul_of_hyperbolic_pairs | exact GlobalTheory.finrank_add_two_mul_of_hyperbolic_pairs | (intros; apply GlobalTheory.finrank_add_two_mul_of_hyperbolic_pairs <;> assumption)
