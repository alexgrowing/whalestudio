import Mathlib

open IsLocalRing

private theorem map_mem_smul_top {R N : Type} [CommRing R] [AddCommGroup N] [Module R N]
    (J : Ideal R) (f : Module.End R N) {x : N} (hx : x ∈ J • (⊤ : Submodule R N)) :
    f x ∈ J • (⊤ : Submodule R N) := by
  have h1 : f x ∈ (J • (⊤ : Submodule R N)).map f := Submodule.mem_map_of_mem hx
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl le_top h1

private theorem pow_mem_pow_smul_top {R N : Type} [CommRing R] [AddCommGroup N] [Module R N]
    (J : Ideal R) (f : Module.End R N) (hf : ∀ x, f x ∈ J • (⊤ : Submodule R N)) (k : ℕ) :
    ∀ x, (f ^ k) x ∈ J ^ k • (⊤ : Submodule R N) := by
  induction k with
  | zero =>
    intro x
    simp
  | succ k ih =>
    intro x
    rw [pow_succ' f k, Module.End.mul_apply, pow_succ J k, Submodule.mul_smul]
    have h1 : f ((f ^ k) x) ∈ (J ^ k • (⊤ : Submodule R N)).map f :=
      Submodule.mem_map_of_mem (ih x)
    rw [Submodule.map_smul''] at h1
    refine Submodule.smul_mono le_rfl ?_ h1
    rintro _ ⟨z, _, rfl⟩
    exact hf z

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locChar :
    ∀ (R N T ι : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup N] [Module R N] [Module.Finite R N] [CommRing T] (ρ : T →+* Module.End R N) (I : Ideal T) (u : ι → T) (e : T), (∀ μ ∈ I, ∀ x, ρ μ x ∈ maximalIdeal R • (⊤ : Submodule R N)) → IsIdempotentElem e → (∀ i, ∃ n : ℕ, u i ^ n * e ∈ I) → 1 - e ∈ I ⊔ Ideal.span (Set.range u) → ∀ x, ρ e x = x ↔ ∀ (i : ι) (k : ℕ), ∃ n : ℕ, (ρ (u i) ^ n) x ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) := by
  intro R N T ι _ _ _ _ _ _ _ ρ I u e hI he hu hspan x
  have hP : ∀ (k : ℕ) (t : T) {z : N}, z ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) →
      ρ t z ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) :=
    fun k t z hz => map_mem_smul_top _ (ρ t) hz
  constructor
  · intro hx i k
    obtain ⟨n, hn⟩ := hu i
    have hek : ∀ j : ℕ, ρ (e ^ j) x = x := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, map_mul, Module.End.mul_apply, hx, ih]
    refine ⟨n * k, ?_⟩
    have hmem := pow_mem_pow_smul_top (maximalIdeal R) (ρ (u i ^ n * e)) (hI _ hn) k x
    have heq : (ρ (u i) ^ (n * k)) x = (ρ (u i ^ n * e) ^ k) x := by
      rw [← map_pow, ← map_pow, mul_pow, ← pow_mul, map_mul, Module.End.mul_apply, hek k]
    rw [heq]
    exact hmem
  · intro h
    obtain ⟨y, hy⟩ : ∃ y, y = ρ (1 - e) x := ⟨_, rfl⟩
    have hyk : ∀ k : ℕ, y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) := by
      intro k
      let S : Ideal T :=
        { carrier := {t | ρ t y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)}
          add_mem' := fun {a b} ha hb => by
            show ρ (a + b) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
            rw [map_add, LinearMap.add_apply]
            exact add_mem ha hb
          zero_mem' := by
            show ρ 0 y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
            rw [map_zero, LinearMap.zero_apply]
            exact zero_mem _
          smul_mem' := fun c t ht => by
            show ρ (c * t) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
            rw [map_mul, Module.End.mul_apply]
            exact hP k c ht }
      have hrad : I ⊔ Ideal.span (Set.range u) ≤ S.radical := by
        refine sup_le (fun μ hμ => Ideal.mem_radical_iff.mpr ⟨k, ?_⟩) (Ideal.span_le.mpr ?_)
        · show ρ (μ ^ k) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
          rw [map_pow]
          exact pow_mem_pow_smul_top _ (ρ μ) (hI μ hμ) k y
        · rintro _ ⟨i, rfl⟩
          obtain ⟨n, hn⟩ := h i k
          refine Ideal.mem_radical_iff.mpr ⟨n, ?_⟩
          show ρ (u i ^ n) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
          have hc : ρ (u i ^ n) y = ρ (1 - e) ((ρ (u i) ^ n) x) := by
            rw [hy, ← map_pow, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
              ← map_mul, mul_comm]
          rw [hc]
          exact hP k _ hn
      obtain ⟨K, hK⟩ := Ideal.mem_radical_iff.mp (hrad hspan)
      have hKy : ρ ((1 - e) ^ K) y = y := by
        rw [hy, ← Module.End.mul_apply, ← map_mul, ← pow_succ, he.one_sub.pow_succ_eq]
      have hK' : ρ ((1 - e) ^ K) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) := hK
      rwa [hKy] at hK'
    have hy0 : y = 0 := IsHausdorff.haus inferInstance y (fun k => SModEq.zero.mpr (hyk k))
    rw [hy, map_sub, map_one, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hy0
    exact hy0.symm
