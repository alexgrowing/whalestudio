import Mathlib

theorem UpperTheory.Reformulated.B.Qe22.aeval_inter :
    ∀ {M N : Type} [inst : AddCommGroup M] [inst_1 : _root_.Module ℂ M]
    [inst_2 : AddCommGroup N] [inst_3 : _root_.Module ℂ N] (f : M →ₗ[ℂ] N) (T : Module.End ℂ M) (T' : Module.End ℂ N),
    (∀ (x : M), (f : M → N) ((T : M → M) x) = (T' : N → N) ((f : M → N) x)) →
      ∀ (p : Polynomial ℂ) (x : M),
        (f : M → N) (((Polynomial.aeval T : Polynomial ℂ → Module.End ℂ M) p : M → M) x) =
          ((Polynomial.aeval T' : Polynomial ℂ → Module.End ℂ N) p : N → N) ((f : M → N) x) := by
  intro M N _ _ _ _ f T T' h p
  have hpow : ∀ (n : ℕ) (x : M), f ((T ^ n) x) = (T' ^ n) (f x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp, hq]
  | monomial n a =>
    intro x
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
      ← Algebra.smul_def, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, hpow]
