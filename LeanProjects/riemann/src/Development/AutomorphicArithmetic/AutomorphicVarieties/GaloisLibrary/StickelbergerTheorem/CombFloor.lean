import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

private theorem combFloor_step (M : ℕ) [NeZero M] (k : ℕ) (t : ZMod M) :
    (k + 1) * t.val / M = k * t.val / M + carry M ((k : ZMod M) * t) (1 * t) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have key : ∀ a v : ℕ, v < M → (a + v) / M = a / M + (if M ≤ a % M + v then 1 else 0) := by
    intro a v hv
    have hr := Nat.mod_lt a hM
    conv_lhs => rw [← Nat.div_add_mod a M, add_assoc, Nat.mul_add_div hM]
    congr 1
    split_ifs with h
    · exact Nat.div_eq_of_lt_le (by omega) (by omega)
    · exact Nat.div_eq_of_lt (by omega)
  have hkt : ((k : ZMod M) * t).val = k * t.val % M := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  show _ = _ + (if M ≤ ((k : ZMod M) * t).val + (1 * t).val then 1 else 0)
  rw [hkt, one_mul, add_mul, one_mul, key _ _ (ZMod.val_lt t)]

theorem UpperTheory.V.Stick.combFloor :
    ∀ (M : ℕ) [NeZero M] (A : Type) [CommGroup A] (x : (ZMod M)ˣ → A),
    (∀ a b : ZMod M, ∏ t : (ZMod M)ˣ, x t ^ carry M (a * t) (b * t) = 1) →
    ∀ k : ℕ, ∏ t : (ZMod M)ˣ, x t ^ (k * (t : ZMod M).val / M) = 1 := by
  intro M _ A _ x hx k
  induction k with
  | zero => simp
  | succ k ih =>
    simp_rw [combFloor_step M k, pow_add]
    rw [Finset.prod_mul_distrib, ih, hx, one_mul]
