import Mathlib

namespace GlobalTheory

open Submodule in

theorem pow_maps_torsion_into_smul_top (R : Type) [CommRing R] [IsDedekindDomain R] (M : Type)
    [AddCommGroup M] [Module R M] (I J : Ideal R) (f : M →ₗ[R] M) (m : ℕ) :
    I.IsMaximal → J ≠ ⊥ → (∀ x, (f ^ m) x ∈ I • (⊤ : Submodule R M)) →
      ∃ j : ℕ, ∀ y : M, (∀ a ∈ I, a • y ∈ J • (⊤ : Submodule R M)) →
        (f ^ j) y ∈ J • (⊤ : Submodule R M) := by
  intro hI hJ hf
  obtain ⟨Q, hIQ, hJQ⟩ := Ideal.eq_prime_pow_mul_coprime hJ I
  set k := Multiset.count I (UniqueFactorizationMonoid.normalizedFactors J)

  have hstab : ∀ (n : ℕ) (z : M), z ∈ J • (⊤ : Submodule R M) → (f ^ n) z ∈ J • (⊤ : Submodule R M) := by
    intro n z hz
    have : (J • (⊤ : Submodule R M)).map (f ^ n) ≤ J • (⊤ : Submodule R M) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact this ⟨z, hz, rfl⟩

  have hmap : (⊤ : Submodule R M).map (f ^ m) ≤ I • (⊤ : Submodule R M) := by
    rintro _ ⟨x, -, rfl⟩
    exact hf x
  have hpow : ∀ (i : ℕ) (x : M), (f ^ (m * i)) x ∈ I ^ i • (⊤ : Submodule R M) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      have h1 : (f ^ (m * (i + 1))) x = (f ^ m) ((f ^ (m * i)) x) := by
        rw [Nat.mul_succ, add_comm, pow_add, Module.End.mul_apply]
      rw [h1]
      have h2 : (I ^ i • (⊤ : Submodule R M)).map (f ^ m) ≤ I ^ (i + 1) • (⊤ : Submodule R M) := by
        rw [Submodule.map_smul'', pow_succ, Submodule.mul_smul]
        exact Submodule.smul_mono le_rfl hmap
      exact h2 ⟨_, ih x, rfl⟩
  refine ⟨m * k, fun y hy => ?_⟩
  set Z := (f ^ (m * k)) y with hZ
  have hZk : Z ∈ I ^ k • (⊤ : Submodule R M) := hpow k y
  have hIZ : ∀ a ∈ I, a • Z ∈ J • (⊤ : Submodule R M) := by
    intro a ha
    rw [hZ, ← LinearMap.map_smul]
    exact hstab _ _ (hy a ha)
  have hJle : J ≤ Q := by rw [hJQ]; exact Ideal.mul_le_inf.trans inf_le_right
  have hZQ : Z ∈ Q • (⊤ : Submodule R M) := by
    have h1 : (1 : R) ∈ I ⊔ Q := by rw [hIQ]; trivial
    obtain ⟨t, ht, s, hs, hts⟩ := Submodule.mem_sup.1 h1
    have : Z = t • Z + s • Z := by rw [← add_smul, hts, one_smul]
    rw [this]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem_smul hs trivial)
    exact Submodule.smul_mono_left hJle (hIZ t ht)
  have hkQ : I ^ k ⊔ Q = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq] at hIQ ⊢
    exact hIQ.pow_left
  have h1 : (1 : R) ∈ I ^ k ⊔ Q := by rw [hkQ]; trivial
  obtain ⟨t, ht, s, hs, hts⟩ := Submodule.mem_sup.1 h1
  have : Z = t • Z + s • Z := by rw [← add_smul, hts, one_smul]
  rw [this]
  refine Submodule.add_mem _ ?_ ?_
  · have : t • Z ∈ I ^ k • Q • (⊤ : Submodule R M) := Submodule.smul_mem_smul ht hZQ
    rwa [← Submodule.mul_smul, ← hJQ] at this
  · have : s • Z ∈ Q • I ^ k • (⊤ : Submodule R M) := Submodule.smul_mem_smul hs hZk
    rwa [← Submodule.mul_smul, mul_comm, ← hJQ] at this

end GlobalTheory
