import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.comap_pow_le :
    ∀ {A M M' : Type} [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] [Module.Finite A M'] (I : Ideal A) (f : M →ₗ[A] M'), ∃ c : ℕ, ∀ m : ℕ, (I ^ (m + c) • (⊤ : Submodule A M')).comap f ≤ LinearMap.ker f ⊔ I ^ m • (⊤ : Submodule A M) := by
  intro A M M' _ _ _ _ _ _ _ I f
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
  refine ⟨k, fun m x hx => ?_⟩
  have h1 : f x ∈ I ^ (m + k) • (⊤ : Submodule A M') ⊓ LinearMap.range f :=
    ⟨hx, LinearMap.mem_range_self f x⟩
  rw [hk (m + k) (Nat.le_add_left k m), Nat.add_sub_cancel] at h1
  have h2 : f x ∈ I ^ m • LinearMap.range f :=
    Submodule.smul_mono le_rfl inf_le_right h1
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h2
  have h3 : x ∈ ((I ^ m • (⊤ : Submodule A M)).map f).comap f := h2
  rw [Submodule.comap_map_eq, sup_comm] at h3
  exact h3
