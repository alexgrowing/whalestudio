import Mathlib

theorem UpperTheory.exists_dirichletCharacter_prime_of_orderOf_dvd :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N) (p : ℕ), p.Prime → orderOf ψ ∣ p - 1 → ∃ ξ : DirichletCharacter O p, orderOf ξ = orderOf ψ := by
  intro O _ _ N _ ψ p hp hd
  haveI := Fact.mk hp
  have hfin : Finite ψ.toUnitHom.range :=
    Finite.of_surjective _ ψ.toUnitHom.rangeRestrict_surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ψ.toUnitHom.range)
  obtain ⟨u0, hu0⟩ := g.2
  have key : orderOf ψ = orderOf (g : Oˣ) := by
    rw [orderOf_eq_orderOf_iff]
    intro k
    constructor
    · intro h
      apply Units.ext
      rw [← hu0, Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, h,
        MulChar.one_apply_coe, Units.val_one]
    · intro h
      refine MulChar.ext fun u => ?_
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨ψ.toUnitHom u, u, rfl⟩)
      have hm' : (g : Oˣ) ^ m = ψ.toUnitHom u := by
        rw [← Subgroup.coe_zpow, hm]
      rw [← MulChar.coe_toUnitHom, ← hm', ← Units.val_pow_eq_pow_val, ← zpow_natCast,
        ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow, Units.val_one]
  have hmem : (g : Oˣ) ∈ rootsOfUnity (Fintype.card (ZMod p)ˣ) O := by
    rw [mem_rootsOfUnity, ZMod.card_units p]
    exact orderOf_dvd_iff_pow_eq_one.1 (key ▸ hd)
  refine ⟨(MulChar.equiv_rootsOfUnity (ZMod p) O).symm ⟨g, hmem⟩, ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, key]
