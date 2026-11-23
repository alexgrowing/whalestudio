import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection

theorem UpperTheory.Reformulated.B.PrimeApproximation.yPrime_approx :
    ∀ {R σ : Type} [inst : CommRing R] {y : σ → R} {f : R} {BB : Type} [inst_1 : CommRing BB] [inst_2 : Algebra R BB],
      UpperTheory.V.Pa.Core.IsYCpl y f BB →
        ∀ (n : ℕ) (J : Ideal R),
          ∀ x ∈ Ideal.map (Algebra.algebraMap R BB) J,
            ∃ (k : ℕ),
              ∃ a ∈ J,
                (Algebra.algebraMap R BB : R → BB) f ^ k * x - (Algebra.algebraMap R BB : R → BB) a ∈
                  Ideal.map (Algebra.algebraMap R BB) (Ideal.span (Set.range y) ^ n) := by
  intro R σ _ y f BB _ _ h n J x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨0, a, ha, ?_⟩
    rw [pow_zero, one_mul, sub_self]
    exact Ideal.zero_mem _
  · refine ⟨0, 0, J.zero_mem, ?_⟩
    rw [mul_zero, map_zero, sub_self]
    exact Ideal.zero_mem _
  · rintro u v - - ⟨k, a, ha, hu⟩ ⟨m, b, hb, hv⟩
    refine ⟨k + m, f ^ m * a + f ^ k * b,
      J.add_mem (J.mul_mem_left _ ha) (J.mul_mem_left _ hb), ?_⟩
    have key := Ideal.add_mem _
      (Ideal.mul_mem_left _ (algebraMap R BB f ^ m) hu)
      (Ideal.mul_mem_left _ (algebraMap R BB f ^ k) hv)
    convert key using 1
    simp only [map_add, map_mul, map_pow]
    ring
  · rintro c u - ⟨k, a, ha, hu⟩
    obtain ⟨j, r, hr⟩ := h.dense n c
    refine ⟨j + k, r * a, J.mul_mem_left _ ha, ?_⟩
    have key := Ideal.add_mem _
      (Ideal.mul_mem_left _ (algebraMap R BB f ^ j * c) hu)
      (Ideal.mul_mem_right (algebraMap R BB a) _ hr)
    convert key using 1
    simp only [map_mul, smul_eq_mul]
    ring
