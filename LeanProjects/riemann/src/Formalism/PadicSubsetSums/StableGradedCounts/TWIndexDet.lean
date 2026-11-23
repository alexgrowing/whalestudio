import Formalism.PadicSubsetSums.StableGradedCounts.TWIndexAdditive

open Module

namespace Formalism.IrreducibleCountingLemmas.TW

namespace Idx

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]

theorem valuation_unique {ϖ : O} (hϖ : Irreducible ϖ) (u v : Oˣ) (a : ℤ) (m : ℕ)
    (h : algebraMap O K u * algebraMap O K ϖ ^ a
      = algebraMap O K v * algebraMap O K ϖ ^ (a + (m : ℤ))) : m = 0 := by
  have hπ : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero
  rw [zpow_add₀ hπ, zpow_natCast, mul_comm (_ ^ a), ← mul_assoc] at h
  have h2 := mul_right_cancel₀ (zpow_ne_zero a hπ) h
  rw [← map_pow, ← map_mul] at h2
  have h3 := IsFractionRing.injective O K h2
  by_contra hm
  have : IsUnit (ϖ ^ m) := isUnit_of_mul_isUnit_right (h3 ▸ u.isUnit)
  exact hϖ.not_isUnit ((isUnit_pow_iff hm).1 this)

theorem val_unique {ϖ : O} (hϖ : Irreducible ϖ) (u v : Oˣ) (a b : ℤ)
    (h : algebraMap O K u * algebraMap O K ϖ ^ a = algebraMap O K v * algebraMap O K ϖ ^ b) :
    a = b := by
  rcases le_total a b with hab | hab
  · obtain ⟨m, rfl⟩ := Int.le.dest hab
    have := valuation_unique hϖ u v a m h
    simp [this]
  · obtain ⟨m, rfl⟩ := Int.le.dest hab
    have := valuation_unique hϖ v u b m h.symm
    simp [this]

end Idx

theorem index_of_determinant : IndexDet := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ d b w ϖ u n hϖ hdet
  have hinj := IsFractionRing.injective O K
  have hπ : algebraMap O K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have hu : algebraMap O K (u : O) ≠ 0 := (map_ne_zero_iff _ hinj).2 u.ne_zero
  have hne : b.det w ≠ 0 := by
    rw [hdet]; exact mul_ne_zero hu (zpow_ne_zero _ hπ)
  have hb := (b.is_basis_iff_det).2 (isUnit_iff_ne_zero.2 hne)
  obtain ⟨wb, rfl⟩ : ∃ wb : Basis (Fin d) K V, ⇑wb = w :=
    ⟨Basis.mk hb.1 hb.2.ge, Basis.coe_mk _ _⟩
  have hB := Idx.isLat_span_basis (O := O) b
  have hW := Idx.isLat_span_basis (O := O) wb
  have hQ := Idx.isLat_inf hB hW
  obtain ⟨n', γ, hγ⟩ := Idx.exists_basis hQ
  have hn : n' = d := by
    have h1 := Module.finrank_eq_card_basis b
    have h2 := Module.finrank_eq_card_basis γ
    simpa using h2.symm.trans h1
  subst hn
  obtain ⟨D1, hD1, l1⟩ := Idx.relLen_span_of_le (O := O) b γ (hγ ▸ inf_le_left)
    (b.isUnit_det γ).ne_zero
  obtain ⟨D2, hD2, l2⟩ := Idx.relLen_span_of_le (O := O) wb γ (hγ ▸ inf_le_right)
    (wb.isUnit_det γ).ne_zero
  have hD1ne : D1 ≠ 0 := by
    rintro rfl; rw [map_zero] at hD1; exact (b.isUnit_det γ).ne_zero hD1.symm
  have hD2ne : D2 ≠ 0 := by
    rintro rfl; rw [map_zero] at hD2; exact (wb.isUnit_det γ).ne_zero hD2.symm
  rw [Idx.sIdx_eq_sub hB hW hQ inf_le_left inf_le_right, ← hγ, l1, l2]
  obtain ⟨k1, u1, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hD1ne hϖ
  obtain ⟨k2, u2, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hD2ne hϖ
  rw [Idx.ord_unit_mul_pow hϖ, Idx.ord_unit_mul_pow hϖ, ENat.toNat_natCast, ENat.toNat_natCast]
  have hmul := b.det_mul_det wb γ
  rw [← hD1, ← hD2, hdet] at hmul
  have key : (k1 : ℤ) = n + k2 := by
    apply Idx.val_unique (K := K) hϖ u1 (u * u2)
    rw [zpow_add₀ hπ, zpow_natCast, zpow_natCast, Units.val_mul, map_mul]
    rw [map_mul, map_mul, map_pow, map_pow] at hmul
    rw [← hmul]; ring
  omega

end Formalism.IrreducibleCountingLemmas.TW
