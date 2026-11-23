import Mathlib

namespace GlobalTheory.PolynomialEvaluationMembership

theorem pow_apply_mem {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g : Module.End F V) (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (n : ℕ) :
    ∀ x ∈ W, (g ^ n) x ∈ W := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hW x hx)

theorem aeval_apply_mem {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g : Module.End F V) (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (p : Polynomial F) :
    ∀ x ∈ W, (Polynomial.aeval g p) x ∈ W := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x hx
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem (hp x hx) (hq x hx)
  | monomial n a =>
    intro x hx
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact W.smul_mem a (pow_apply_mem g W hW n x hx)

end GlobalTheory.PolynomialEvaluationMembership
