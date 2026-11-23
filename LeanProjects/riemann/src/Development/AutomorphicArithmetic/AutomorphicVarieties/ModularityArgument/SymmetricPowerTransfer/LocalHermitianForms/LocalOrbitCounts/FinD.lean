import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsOfGOrbNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.MemRangeIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FinBetween
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.StabG

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Loc.finD : UpperTheory.V.Z.Sym.Loc.FinD := by
  classical
  intro O K _ _ _ _ _ Δ τ L hτ γ j hγ hj
  obtain ⟨φ, h1, h2, -, h4⟩ := dIso O K Δ L
  obtain ⟨j', hj'γ, hj'tr, hj'⟩ := h4 τ γ j hγ hj
  have hZD : ∀ g : DX Δ, g ∈ ZD Δ ↔ ∃ z, IsScal z g := by
    intro g
    simp only [ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.comp_apply, IsScal]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      show ((g : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = _
      rw [← hz]
      first | rfl | simp [Matrix.GeneralLinearGroup.scalar]
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      apply Units.ext
      rw [show ((g : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = Glob.mt g from rfl, hz]
      first | rfl | simp [Matrix.GeneralLinearGroup.scalar]
  have hmap : (ZD Δ ⊔ KD Δ O).map φ.toMonoidHom = ZK O K := by
    rw [Subgroup.map_sup]
    unfold ZK
    congr 1
    · ext x
      rw [Subgroup.mem_map_equiv, hZD, MonoidHom.mem_range]
      constructor
      · rintro ⟨z, hz⟩
        exact ⟨z, by rw [← (h2 z _).1 hz]; simp⟩
      · rintro ⟨z, rfl⟩
        exact ⟨z, (h2 z _).2 (by simp)⟩
    · ext x
      rw [Subgroup.mem_map_equiv, ← h1]
      simp
  have hmem : ∀ g, g ∈ ZD Δ ⊔ KD Δ O ↔ φ g ∈ ZK O K := by
    intro g
    rw [← hmap, Subgroup.mem_map_equiv]
    simp
  have hgen : ∀ z : (Etau K τ)ˣ, (z : Etau K τ).im ≠ 0 → ∃ S : Finset (DX Δ), ∀ y : DX Δ,
      y⁻¹ * j z * y ∈ ZD Δ ⊔ KD Δ O → ∃ t, ∃ s ∈ S, ∃ u ∈ ZD Δ ⊔ KD Δ O, y = j t * s * u := by
    intro z hz
    obtain ⟨s, hs⟩ := finG O K Δ τ L hτ j' hj'tr z hz
    refine ⟨s.image φ.symm, ?_⟩
    intro y hy
    rw [hmem] at hy
    simp only [map_mul, map_inv, hj'] at hy
    obtain ⟨t, x, hx, k, hk, hyk⟩ := hs (φ y) hy
    refine ⟨t, φ.symm x, Finset.mem_image_of_mem _ hx, φ.symm k, by rw [hmem]; simp [hk], ?_⟩
    apply φ.injective
    simp [map_mul, hj', hyk]
  obtain ⟨a, ha⟩ := exists_a (K := K) (τ := τ)
  have hγa : γ = j a := by
    apply φ.injective
    rw [hj']
    apply Units.ext
    rw [← hj'γ]
    simp [ha]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := hgen a (by rw [ha]; simp)
    refine ⟨S, ?_⟩
    intro y hy
    apply hS y
    have hK : y⁻¹ * γ * y ∈ KD Δ O := by
      by_contra hn
      apply hy
      simp [one, hn]
    rw [← hγa]
    exact Subgroup.mem_sup_right hK
  · intro z hz χ
    obtain ⟨S, hS⟩ := hgen z (by rw [hz]; simp)
    refine ⟨S, ?_⟩
    intro y hy
    apply hS y
    unfold fZD at hy
    split_ifs at hy with hh
    · obtain ⟨z0, s0, hsc, hk⟩ := hh
      have hs0 : s0 ∈ ZD Δ := (hZD s0).2 ⟨z0, hsc⟩
      have := (ZD Δ ⊔ KD Δ O).mul_mem (Subgroup.mem_sup_left hs0) (Subgroup.mem_sup_right hk)
      simpa using this
    · exact absurd rfl hy
  · intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hst : Subgroup.comap j (MulAction.stabilizer (DX Δ) (g : DX Δ ⧸ ZD Δ ⊔ KD Δ O)) =
        Subgroup.comap (jU j') (Subgroup.comap (MulAut.conj (φ g)⁻¹).toMonoidHom (ZK O K)) := by
      ext t
      simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk,
        smul_eq_mul, QuotientGroup.eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [← Subgroup.inv_mem_iff, show ((j t * g)⁻¹ * g)⁻¹ = g⁻¹ * j t * g by group, hmem]
      simp [hj']
    rw [hst]
    exact stabG O K Δ τ L hτ j' hj'tr (φ g)
