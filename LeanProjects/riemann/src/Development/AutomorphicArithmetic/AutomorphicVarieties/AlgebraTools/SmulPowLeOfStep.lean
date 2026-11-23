import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.smul_pow_le_of_step :
    ∀ (R : Type) [CommRing R] (𝔞 I 𝔶 : Ideal R) (f : R),
      (∀ (X : Type) [AddCommGroup X] [Module R X] (X₀ : Type) [AddCommGroup X₀] [Module R X₀] (φ : X₀ →ₗ[R] X) (ψ : X →ₗ[R] X₀) (n : R), (∀ x, φ (ψ x) = n • x) → n ∣ f →
        (𝔞 • ⊤ : Submodule R X₀) ≤ I • ⊤ → ((Ideal.span {f} * 𝔞) • ⊤ : Submodule R X) ≤ I • ⊤) ∧
      (∀ (M : Type) [AddCommGroup M] [Module R M], ((Ideal.span {f} * 𝔞) • ⊤ : Submodule R M) ≤ (I ⊔ 𝔶) • ⊤ →
        ∀ k : ℕ, ((Ideal.span {f ^ k} * 𝔞 ^ k) • ⊤ : Submodule R M) ≤ (I ⊔ 𝔶 ^ k) • ⊤) := by
  intro R _ 𝔞 I 𝔶 f
  refine ⟨?_, ?_⟩
  · intro X _ _ X₀ _ _ φ ψ n hn hnf h
    obtain ⟨c, rfl⟩ := hnf
    refine Submodule.smul_le.2 ?_
    intro r hr x _
    obtain ⟨a, ha, rfl⟩ := Ideal.mem_span_singleton_mul.1 hr
    have h1 : a • ψ x ∈ (I • ⊤ : Submodule R X₀) :=
      h (Submodule.smul_mem_smul ha Submodule.mem_top)
    have h2 : φ (a • ψ x) ∈ (I • ⊤ : Submodule R X) := by
      have h3 : φ (a • ψ x) ∈ (I • ⊤ : Submodule R X₀).map φ := Submodule.mem_map_of_mem h1
      rw [Submodule.map_smul''] at h3
      exact Submodule.smul_mono le_rfl le_top h3
    have h4 : (n * c * a) • x = c • φ (a • ψ x) := by
      rw [map_smul, hn, smul_smul, smul_smul]
      congr 1
      ring
    rw [h4]
    exact Submodule.smul_mem _ c h2
  · intro M _ _ h k
    rw [← Ideal.span_singleton_pow, ← mul_pow]
    generalize Ideal.span {f} * 𝔞 = b at h
    induction k with
    | zero => simp
    | succ k ih =>
      have hle : (I ⊔ 𝔶 ^ k) * (I ⊔ 𝔶) ≤ I ⊔ 𝔶 ^ (k + 1) := by
        rw [Ideal.sup_mul, Ideal.mul_sup (𝔶 ^ k), pow_succ]
        refine sup_le (le_sup_of_le_left Ideal.mul_le_left) (sup_le (le_sup_of_le_left Ideal.mul_le_right) le_sup_right)
      calc (b ^ (k + 1) • ⊤ : Submodule R M) = b • (b ^ k • ⊤) := by
            rw [pow_succ', mul_smul]
        _ ≤ b • ((I ⊔ 𝔶 ^ k) • ⊤) := smul_mono_right b ih
        _ = (I ⊔ 𝔶 ^ k) • (b • ⊤) := by
            rw [← mul_smul, ← mul_smul, mul_comm]
        _ ≤ (I ⊔ 𝔶 ^ k) • ((I ⊔ 𝔶) • ⊤) := smul_mono_right _ h
        _ = ((I ⊔ 𝔶 ^ k) * (I ⊔ 𝔶)) • ⊤ := by rw [mul_smul]
        _ ≤ (I ⊔ 𝔶 ^ (k + 1)) • ⊤ := Submodule.smul_mono_left hle
