import Mathlib

theorem UpperTheory.Reformulated.B.Qg1.exists_pow_mem_of_mul_mem_pow :
    ∀ {A : Type} [inst : CommRing A] [IsNoetherianRing A] (m : Ideal A) (δ : A),
    (∀ (a : A), δ * a = (0 : A) → a = (0 : A)) → ∀ (j : ℕ), ∃ (k : ℕ), j ≤ k ∧ ∀ (a : A), δ * a ∈ m ^ k → a ∈ m ^ j := by
  intro A _ _ m δ hδ j
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul m (Ideal.span {δ} : Submodule A A)
  refine ⟨j + c, Nat.le_add_right j c, fun a ha => ?_⟩
  have h1 : δ * a ∈ (m ^ (j + c) • ⊤ ⊓ (Ideal.span {δ} : Submodule A A) : Submodule A A) := by
    refine ⟨?_, Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self δ)⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact ha
  rw [hc (j + c) (Nat.le_add_left c j), Nat.add_sub_cancel] at h1
  have h2 : δ * a ∈ Ideal.span {δ} * m ^ j := by
    rw [mul_comm (Ideal.span {δ}), ← Ideal.smul_eq_mul]
    exact Submodule.smul_mono le_rfl inf_le_right h1
  obtain ⟨z, hz, hza⟩ := Ideal.mem_span_singleton_mul.mp h2
  have h3 : a - z = 0 := hδ _ (by rw [mul_sub, hza, sub_self])
  rw [sub_eq_zero.mp h3]
  exact hz
