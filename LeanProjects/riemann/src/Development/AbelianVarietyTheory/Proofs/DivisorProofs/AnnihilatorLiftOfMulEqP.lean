import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem annihilator_lift_of_mul_eq_p : ∀ (p : ℕ) (O : Type) [CommRing O] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k), (p : k) = 0 → (p : Λ) ^ 2 = 0 → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] O) M] [IsScalarTower Λ (Λ ⊗[ℤ] O) M], (∀ m : M, (p : Λ) • m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M)) → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] O) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom] N), Function.Surjective f → (∀ m, f m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M)) → ∀ ϖ z : O, ϖ * z - (p : O) ∈ Ideal.span {(p : O) ^ 2} → ∀ n : N, ((1 : k) ⊗ₜ[ℤ] ϖ) • n = 0 → n ∈ Ideal.span {a : k ⊗[ℤ] O | ((1 : k) ⊗ₜ[ℤ] ϖ) * a = 0} • (⊤ : Submodule (k ⊗[ℤ] O) N) := by
  intro p O _ Λ _ k _ π hpk hp2 M _ _ _ _ htor N _ _ f hf hker ϖ z hϖz n hn
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hϖz

  have hL : ∀ (c : Λ) (m : M), c • m = (c ⊗ₜ[ℤ] (1 : O)) • m := by
    intro c m
    rw [← smul_one_smul (Λ ⊗[ℤ] O) c m]
    congr 1
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

  have hp2M : ∀ m : M, ((p : Λ) ^ 2) • m = 0 := by intro m; rw [hp2, zero_smul]

  have hpz : ∀ m : M, (p : Λ) • m = ((1 : Λ) ⊗ₜ[ℤ] z) • ((1 : Λ) ⊗ₜ[ℤ] ϖ) • m := by
    intro m
    rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm z ϖ]
    have : ϖ * z = (p : O) + y * (p : O) ^ 2 := by linear_combination -hy
    rw [this, TensorProduct.tmul_add, add_smul]
    have h1 : ((1 : Λ) ⊗ₜ[ℤ] (p : O)) = ((p : Λ) ⊗ₜ[ℤ] (1 : O)) := by
      have e1 : (p : O) = p • (1 : O) := by simp
      have e2 : (p : Λ) = p • (1 : Λ) := by simp
      rw [e1, e2, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    have h2 : ((1 : Λ) ⊗ₜ[ℤ] (y * (p : O) ^ 2)) = ((p : Λ) ^ 2) • ((1 : Λ) ⊗ₜ[ℤ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [show (y * (p : O) ^ 2) = ((p ^ 2 : ℕ) : ℤ) • y by push_cast; simp [zsmul_eq_mul]; ring]
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      congr 1
      push_cast; simp [zsmul_eq_mul]
    rw [h1, h2, ← hL, smul_assoc, hp2M, add_zero]

  have hσp : ∀ m : M, f ((p : Λ) • m) = 0 := by
    intro m
    rw [hL, f.map_smulₛₗ]
    have : (Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom ((p : Λ) ⊗ₜ[ℤ] (1 : O)) = 0 := by
      simp [Algebra.TensorProduct.map_tmul, hpk]
    rw [this, zero_smul]
  have hf0 : ∀ m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M), f m = 0 := by
    intro m hm
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hm
    obtain ⟨b, -, rfl⟩ := hm
    exact hσp b
  have hσϖ : (Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom ((1 : Λ) ⊗ₜ[ℤ] ϖ) = (1 : k) ⊗ₜ[ℤ] ϖ := by
    simp [Algebra.TensorProduct.map_tmul]
  have hσz : (Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom ((1 : Λ) ⊗ₜ[ℤ] z) = (1 : k) ⊗ₜ[ℤ] z := by
    simp [Algebra.TensorProduct.map_tmul]
  obtain ⟨m, rfl⟩ := hf n
  have h1 : f (((1 : Λ) ⊗ₜ[ℤ] ϖ) • m) = 0 := by rw [f.map_smulₛₗ, hσϖ]; exact hn
  have h2 := hker _ h1
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨m', -, hm'⟩ := h2
  have h3 : ((1 : Λ) ⊗ₜ[ℤ] ϖ) • (m - ((1 : Λ) ⊗ₜ[ℤ] z) • m') = 0 := by
    rw [smul_sub, ← hm', smul_smul, mul_comm ((1 : Λ) ⊗ₜ[ℤ] ϖ), ← smul_smul, ← hpz, sub_self]
  have h4 : (p : Λ) • (m - ((1 : Λ) ⊗ₜ[ℤ] z) • m') = 0 := by
    rw [hpz, h3, smul_zero]
  have h5 := hf0 _ (htor _ h4)
  have hn' : f m = ((1 : k) ⊗ₜ[ℤ] z) • f m' := by
    rw [map_sub, f.map_smulₛₗ, hσz, sub_eq_zero] at h5; exact h5
  rw [hn']
  apply Submodule.smul_mem_smul _ Submodule.mem_top
  apply Ideal.subset_span
  show ((1 : k) ⊗ₜ[ℤ] ϖ) * ((1 : k) ⊗ₜ[ℤ] z) = 0
  have hw : ϖ * z = ((p : ℤ) • (1 + (p : O) * y)) := by rw [zsmul_eq_mul]; push_cast; linear_combination -hy
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hw, ← TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]
  push_cast
  rw [hpk, TensorProduct.zero_tmul]

end GlobalTheory
