import Mathlib

namespace GlobalTheory.AevalCommute

theorem pow_apply_comm {O : Type} [CommRing O] {k : Type} [Field k] [Algebra O k]
    {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module k V]
    (J : M →+ V) (ν : Module.End O M) (μ : Module.End k V)
    (hνμ : ∀ y : M, J (ν y) = μ (J y)) (n : ℕ) (y : M) :
    J ((ν ^ n) y) = (μ ^ n) (J y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hνμ]

theorem aeval_apply_comm {O : Type} [CommRing O] {k : Type} [Field k] [Algebra O k]
    {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module k V]
    (J : M →+ V) (hJ : ∀ (c : O) (y : M), J (c • y) = algebraMap O k c • J y)
    (ν : Module.End O M) (μ : Module.End k V)
    (hνμ : ∀ y : M, J (ν y) = μ (J y)) (f : Polynomial O) (y : M) :
    J (Polynomial.aeval ν f y) = Polynomial.aeval μ (f.map (algebraMap O k)) (J y) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, hJ, pow_apply_comm J ν μ hνμ]

theorem main : ∀ {O : Type} [inst : CommRing O] {k : Type} [inst_1 : Field k] [inst_2 : Algebra O k] {M V : Type} [inst_3 : AddCommGroup M] [inst_4 : Module O M] [inst_5 : AddCommGroup V] [inst_6 : Module k V] (J : M →+ V), (∀ (c : O) (y : M), (J : M → V) (c • y) = (Algebra.algebraMap O k : O → k) c • (J : M → V) y) → ∀ (ν : Module.End O M) (μ : Module.End k V), (∀ (y : M), (J : M → V) ((ν : M → M) y) = (μ : V → V) ((J : M → V) y)) → ∀ (f : Polynomial O) (y : M), (J : M → V) (((Polynomial.aeval ν : Polynomial O → Module.End O M) f : M → M) y) = ((Polynomial.aeval μ : Polynomial k → Module.End k V) (Polynomial.map (Algebra.algebraMap O k) f) : V → V) ((J : M → V) y) :=
  fun J hJ ν μ hνμ f y => aeval_apply_comm J hJ ν μ hνμ f y

end GlobalTheory.AevalCommute
