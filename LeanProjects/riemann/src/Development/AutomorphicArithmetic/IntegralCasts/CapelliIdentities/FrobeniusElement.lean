import Mathlib

noncomputable def UpperTheory.Reformulated.B.FrobeniusElement.frb :
    {l : ℕ} → [Fact (Nat.Prime l)] → {B₀ : Type} → [inst : CommRing B₀] → (↑l : B₀) = (0 : B₀) → B₀ →+* B₀ :=
  fun {l} [hl : Fact (Nat.Prime l)] {B₀} [CommRing B₀] h =>
    { toFun := fun x => x ^ l
      map_one' := one_pow l
      map_mul' := fun x y => mul_pow x y l
      map_zero' := zero_pow hl.out.ne_zero
      map_add' := fun x y => by
        obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl.out x y
        rw [hr, h]
        ring }
