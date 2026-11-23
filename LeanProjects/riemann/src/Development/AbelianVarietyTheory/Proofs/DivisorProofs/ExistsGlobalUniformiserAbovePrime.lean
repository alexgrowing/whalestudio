import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem exists_global_uniformiser_above_prime :
    ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F], ∃ ϖ z : 𝓞 F,
      ϖ * z - (p : 𝓞 F) ∈ Ideal.span {(p : 𝓞 F) ^ 2} ∧ (∃ n : ℕ, ϖ ^ n ∈ Ideal.span {(p : 𝓞 F)}) ∧
      IsReduced (𝓞 F ⧸ Ideal.span {(p : 𝓞 F), ϖ}) := by
  intro p hp F _ _
  set J : Ideal (𝓞 F) := (Ideal.span {(p : 𝓞 F)}).radical with hJdef
  have hp0 : (p : 𝓞 F) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := 𝓞 F)).mpr hp.out.ne_zero
  have hI0 : Ideal.span {(p : 𝓞 F) ^ 2} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero _ hp0
  have hpJ : (p : 𝓞 F) ∈ J := Ideal.le_radical (Ideal.mem_span_singleton_self _)
  have hIJ : Ideal.span {(p : 𝓞 F) ^ 2} ≤ J := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact J.pow_mem_of_mem hpJ 2 two_pos
  obtain ⟨ϖ, hϖ⟩ := IsDedekindDomain.exists_sup_span_eq hIJ hI0
  have hϖJ : ϖ ∈ J := hϖ ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  refine ⟨ϖ, ?_⟩

  have hp' : (p : 𝓞 F) ∈ Ideal.span {(p : 𝓞 F) ^ 2} ⊔ Ideal.span {ϖ} := hϖ ▸ hpJ
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hp'
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨z, ?_, hϖJ, ?_⟩
  · have : ϖ * z - (p : 𝓞 F) = -a := by rw [← hab]; ring
    rw [this]; exact neg_mem ha
  · have hK : Ideal.span {(p : 𝓞 F), ϖ} = J := by
      apply le_antisymm
      · rw [Ideal.span_le]
        intro x hx
        rcases hx with rfl | hx
        · exact hpJ
        · rw [Set.mem_singleton_iff] at hx; subst hx; exact hϖJ
      · rw [← hϖ]
        apply sup_le
        · rw [Ideal.span_le, Set.singleton_subset_iff]
          rw [pow_two]
          exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
        · rw [Ideal.span_le, Set.singleton_subset_iff]
          exact Ideal.subset_span (by simp)
    rw [hK]
    exact (Ideal.isRadical_iff_quotient_reduced J).mp (Ideal.radical_isRadical _)

end GlobalTheory
