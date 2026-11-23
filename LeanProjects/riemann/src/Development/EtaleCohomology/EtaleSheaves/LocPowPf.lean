import Development.EtaleCohomology.EtaleSheaves.AugBijPf

noncomputable section
open Polynomial IsLocalRing

namespace LateralTheory.E.LocPowPf

theorem pow_eq_one_of_aeval {q : ℕ} {A : Type} [CommRing A] (ξ : A) (h : aeval ξ (cyclotomic q ℤ) = 0) : ξ ^ q = 1 := by
  obtain ⟨p, hp⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval ξ) hp
  rw [map_mul, h, zero_mul, map_sub, map_pow, aeval_X, map_one] at this
  exact sub_eq_zero.1 this

theorem prim_res {q : ℕ} {A : Type} [CommRing A] [IsLocalRing A] (ξ : GlobalTheory.EtC.Prim q A) :
    IsPrimitiveRoot (residue A ξ.1) q := by
  have hu : IsUnit ((q : ResidueField A)) := by simpa using ξ.2.1.map (residue A)
  have : NeZero (q : ResidueField A) := ⟨hu.ne_zero⟩
  obtain ⟨x, -, hx⟩ := ξ
  change IsPrimitiveRoot (residue A x) q
  rw [← isRoot_cyclotomic_iff, IsRoot, ← map_cyclotomic_int, eval_map]
  change aeval ((residue A).toIntAlgHom x) (cyclotomic q ℤ) = 0
  rw [aeval_algHom_apply, hx, map_zero]

theorem LocPow_of : LateralTheory.E.AugBijPf.LocPow := by
  intro q A _ _ ξ ζ
  have hq : IsUnit (q : A) := ξ.2.1
  have hz := prim_res ζ
  have hx := prim_res ξ
  have : NeZero q := ⟨by rintro rfl; simp at hq⟩
  obtain ⟨i, hi, he⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hcop : i.Coprime q := (hz.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (he ▸ hx)
  refine ⟨ZMod.unitOfCoprime i hcop, ?_⟩
  have hval : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
    simp [ZMod.unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hval]
  set η := ζ.1 ^ i with hη
  have h1 : ξ.1 ^ q = 1 := pow_eq_one_of_aeval ξ.1 ξ.2.2
  have h2 : η ^ q = 1 := by rw [hη, ← pow_mul, mul_comm, pow_mul, pow_eq_one_of_aeval ζ.1 ζ.2.2, one_pow]
  have hres : residue A ξ.1 = residue A η := by rw [hη, map_pow]; exact he.symm
  have hηu : residue A η ≠ 0 := hres ▸ hx.ne_zero (NeZero.ne q)
  have hS : IsUnit (∑ j ∈ Finset.range q, ξ.1 ^ j * η ^ (q - 1 - j)) := by
    rw [← residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_mul, map_pow, hres]
    rw [geom_sum₂_self]
    exact mul_ne_zero (by simpa using (hq.map (residue A)).ne_zero) (pow_ne_zero _ hηu)
  have key := (Commute.all ξ.1 η).geom_sum₂_mul q
  rw [h1, h2, sub_self] at key
  exact sub_eq_zero.1 ((hS.mul_right_eq_zero).1 key)

end LateralTheory.E.LocPowPf
