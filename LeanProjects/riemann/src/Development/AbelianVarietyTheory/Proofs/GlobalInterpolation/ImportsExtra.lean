import Mathlib

namespace GlobalTheory.PrimeOrderModule

theorem exists_character (S M : Type) [CommRing S] [AddCommGroup M] [Module S M] (T : ℕ)
    (hT : T.Prime) (hM : Nat.card M = T) :
    ∃ χ : S →+* ZMod T, ∀ (a : S) (m : M), χ a = 0 → a • m = 0 := by
  haveI : Fact T.Prime := ⟨hT⟩
  have hZ : Nat.card (ZMod T) = T := Nat.card_zmod T
  let e : M ≃+ ZMod T := addEquivOfPrimeCardEq hM hZ
  have key : ∀ (a : S) (m : M), e (a • m) = e (a • e.symm 1) * e m := by
    intro a m
    have hm : m = (e m).val • e.symm 1 := by
      apply e.injective
      rw [map_nsmul, e.apply_symm_apply, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    calc e (a • m) = e (a • ((e m).val • e.symm 1)) := by rw [← hm]
      _ = (e m).val • e (a • e.symm 1) := by rw [smul_comm, map_nsmul]
      _ = e (a • e.symm 1) * e m := by
        rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  let χ : S →+* ZMod T :=
    { toFun := fun a => e (a • e.symm 1)
      map_one' := by simp
      map_mul' := fun a b => by rw [mul_smul, key]
      map_zero' := by simp
      map_add' := fun a b => by rw [add_smul, map_add] }
  refine ⟨χ, fun a m h => ?_⟩
  apply e.injective
  have h' : e (a • e.symm 1) = 0 := h
  rw [key, h', zero_mul, map_zero]

end GlobalTheory.PrimeOrderModule
