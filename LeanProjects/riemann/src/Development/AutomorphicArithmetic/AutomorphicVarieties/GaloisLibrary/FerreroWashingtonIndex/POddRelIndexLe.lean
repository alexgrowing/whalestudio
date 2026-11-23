import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

private theorem pOdd_relIndex_le (l : ℕ) (C : Type) [CommGroup C] [Finite C] (B : Subgroup C) :
    (powR C l).relIndex B ≤ Nat.card (B ⊓ torK C l : Subgroup C) := by
  have h1 : powR B l ≤ (powR C l).subgroupOf B := by
    rintro _ ⟨y, rfl⟩
    exact ⟨(y : C), by simp⟩
  have h2 : ((powR C l).subgroupOf B).index ≤ (powR B l).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (Subgroup.index_dvd_of_le h1)
  have h3 : (powR B l).index = Nat.card (torK B l) := by
    have a := Subgroup.index_mul_card (powR B l)
    have b := Subgroup.index_mul_card (torK B l)
    have c : (torK B l).index = Nat.card (powR B l) := Subgroup.index_ker _
    have d : 0 < Nat.card (powR B l) := Nat.card_pos
    rw [c, ← a, mul_comm] at b
    exact (Nat.eq_of_mul_eq_mul_right d b).symm
  have h4 : Nat.card (torK B l) ≤ Nat.card (B ⊓ torK C l : Subgroup C) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨(x.1 : C), x.1.2, ?_⟩ : (B ⊓ torK C l : Subgroup C))) ?_
    · have hx : x.1 ^ l = 1 := x.2
      show (x.1 : C) ^ l = 1
      rw [← Subgroup.coe_pow, hx]; rfl
    · intro x y hxy
      have e := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext e)
  exact h2.trans (h3.le.trans h4)

theorem UpperTheory.V.FW.pOdd :
    ∀ (l : ℕ) (C : Type) [CommGroup C] [Finite C] (J : C →* C), Odd l → (powR C l ⊔ difR J).index ≤ l * Nat.card (minK J ⊓ torK C l : Subgroup C) → (powR C l).index ≤ l * Nat.card (difR J ⊓ torK C l : Subgroup C) ^ 2 := by
  intro l C _ _ J hl h
  obtain ⟨k, hk⟩ := hl
  have h1 : minK J ⊓ torK C l ≤ difR J ⊓ torK C l := by
    rintro x ⟨hx, hx'⟩
    refine ⟨⟨x ^ (k + 1), ?_⟩, hx'⟩
    have a : J x * x = 1 := hx
    have b : x ^ l = 1 := hx'
    have c : J x = x⁻¹ := eq_inv_of_mul_eq_one_left a
    show x ^ (k + 1) / J (x ^ (k + 1)) = x
    rw [map_pow, c, inv_pow, div_inv_eq_mul, ← pow_add,
      show k + 1 + (k + 1) = l + 1 by omega, pow_succ, b, one_mul]
  have h2 : Nat.card (minK J ⊓ torK C l : Subgroup C) ≤ Nat.card (difR J ⊓ torK C l : Subgroup C) :=
    Subgroup.card_le_of_le h1
  have h3 := Subgroup.relIndex_mul_index (le_sup_left : powR C l ≤ powR C l ⊔ difR J)
  rw [Subgroup.relIndex_sup_left] at h3
  have h4 := pOdd_relIndex_le l C (difR J)
  calc (powR C l).index = (powR C l).relIndex (difR J) * (powR C l ⊔ difR J).index := h3.symm
    _ ≤ Nat.card (difR J ⊓ torK C l : Subgroup C) * (l * Nat.card (difR J ⊓ torK C l : Subgroup C)) :=
      Nat.mul_le_mul h4 (h.trans (Nat.mul_le_mul_left _ h2))
    _ = _ := by ring
