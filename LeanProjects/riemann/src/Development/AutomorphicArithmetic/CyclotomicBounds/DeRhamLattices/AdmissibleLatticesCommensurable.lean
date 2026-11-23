import Mathlib

theorem _root_.UpperTheory.KN.admissible_lattices_commensurable :
    ∀ {O LL V : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field LL] [Algebra O LL] [IsFractionRing O LL]
      [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] (Λ A : Submodule O V), Λ.FG → ∀ c : O, c ≠ 0 →
      ∃ μ : O, μ ≠ 0 ∧ ∀ u ∈ Λ, μ • u ∈ A → ∃ a ∈ A, μ • u = c • a := by
  intro O LL V _ _ _ _ _ _ _ _ _ _ Λ A hΛ c hc
  haveI : IsNoetherian O Λ := isNoetherian_of_fg_of_noetherian Λ hΛ
  let f : ℕ →o Submodule O Λ :=
    ⟨fun n => (A.comap ((c ^ n) • LinearMap.id : V →ₗ[O] V)).comap Λ.subtype, by
      intro m n hmn x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hx ⊢
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [pow_add, mul_comm, mul_smul]
      exact A.smul_mem _ hx⟩
  obtain ⟨N, hN⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) f
  refine ⟨c ^ (N + 1), pow_ne_zero _ hc, ?_⟩
  intro u hu hμ
  have h1 : (⟨u, hu⟩ : Λ) ∈ f (N + 1) := hμ
  rw [← hN (N + 1) (Nat.le_succ N)] at h1
  have h2 : c ^ N • u ∈ A := h1
  exact ⟨c ^ N • u, h2, by rw [pow_succ, mul_comm, mul_smul]⟩
