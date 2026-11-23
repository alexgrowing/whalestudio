import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

namespace LateralTheory.E.E4

def LeafUnitsFG : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], Group.FG (Bˣ ⧸ (Units.map (algebraMap k B).toMonoidHom).range)

theorem units_range_le_pow (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] :
    (Units.map (algebraMap k B).toMonoidHom).range ≤ (powMonoidHom q : Bˣ →* Bˣ).range := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : k) (Nat.pos_of_ne_zero (NeZero.ne q))
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne q)] at hz
    exact a.ne_zero hz.symm
  refine ⟨Units.map (algebraMap k B).toMonoidHom (Units.mk0 z hz0), ?_⟩
  ext
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_mk0]
  rw [← map_pow, hz]

theorem LeafUnits_of (hFG : LeafUnitsFG) : LeafUnits := by
  intro q _ k B _ _ _ _ _ _
  have hle := units_range_le_pow q k B
  let N := (powMonoidHom q : Bˣ →* Bˣ).range
  let M := (Units.map (algebraMap k B).toMonoidHom).range
  have : Group.FG (Bˣ ⧸ M) := hFG k B
  let φ : Bˣ ⧸ M →* Bˣ ⧸ N := QuotientGroup.map M N (MonoidHom.id _) hle
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨QuotientGroup.mk u, rfl⟩
  have : Group.FG (Bˣ ⧸ N) := Group.fg_of_surjective hφ
  apply CommGroup.finite_of_fg_isMulTorsion
  intro x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨q, Nat.pos_of_ne_zero (NeZero.ne q), ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact ⟨u, rfl⟩

end LateralTheory.E.E4
