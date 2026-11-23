import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassGroupTorsionPrincipalPower
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_group_torsion_principal_power : ∀ (A K : Type) [CommRing A] [IsDomain A] [Module.Finite ℤ A]
    [Field K] [Algebra A K] [IsFractionRing A K] (M : ℤ), M ≠ 0 →
    (∀ I J : Submodule A K, I * J = 1 →
      ∃ x : K, x ≠ 0 ∧ Submodule.span A {x} * I ≤ 1 ∧ (M : K) ∈ Submodule.span A {x} * I) →
    ∀ I J : Submodule A K, I * J = 1 → ∃ e : ℕ, 0 < e ∧ ∃ x : K, I ^ e = Submodule.span A {x} := by
  first | exact @GlobalTheory.exists_pow_eq_span_singleton_of_intCast_mem | exact GlobalTheory.exists_pow_eq_span_singleton_of_intCast_mem | (intros; apply GlobalTheory.exists_pow_eq_span_singleton_of_intCast_mem <;> assumption)
