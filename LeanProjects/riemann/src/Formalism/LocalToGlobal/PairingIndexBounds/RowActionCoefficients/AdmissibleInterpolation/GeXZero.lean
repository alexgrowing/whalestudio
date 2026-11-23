import Mathlib

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

variable {Kc : Type} [Field Kc] (p : ℕ) (Oc : Subring Kc)

def geX (x : Kc) (g : ℝ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℝ) ≤ g * b → x ^ b * (p : Kc) ^ (-a) ∈ Oc

variable {p Oc}

theorem geX_mul {u x : Kc} {g : ℝ} (hu : u ∈ Oc) (hx : geX p Oc x g) : geX p Oc (u * x) g := by
  intro a b hb hab
  rw [mul_pow, mul_assoc]
  exact Oc.mul_mem (Oc.pow_mem hu b) (hx a b hb hab)

theorem geX_zero (g : ℝ) : geX p Oc (0 : Kc) g := by
  intro a b hb _
  rw [zero_pow hb.ne', zero_mul]
  exact Oc.zero_mem

theorem geX_neg {x : Kc} {g : ℝ} (hx : geX p Oc x g) : geX p Oc (-x) g := by
  have h := geX_mul (Oc.neg_mem Oc.one_mem) hx
  simpa using h

theorem geX_add (hval : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc) {x y : Kc} {g : ℝ} (hx : geX p Oc x g) (hy : geX p Oc y g) :
    geX p Oc (x + y) g := by
  intro a b hb hab
  rcases eq_or_ne y 0 with rfl | hy0
  · simpa using hx a b hb hab
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa using hy a b hb hab
  rcases hval (x / y) with h | h
  · have e : (x + y) ^ b * (p : Kc) ^ (-a) = (1 + x / y) ^ b * (y ^ b * (p : Kc) ^ (-a)) := by
      rw [← mul_assoc, ← mul_pow, add_mul, one_mul, div_mul_cancel₀ x hy0, add_comm y x]
    rw [e]
    exact Oc.mul_mem (Oc.pow_mem (Oc.add_mem Oc.one_mem h) b) (hy a b hb hab)
  · rw [inv_div] at h
    have e : (x + y) ^ b * (p : Kc) ^ (-a) = (1 + y / x) ^ b * (x ^ b * (p : Kc) ^ (-a)) := by
      rw [← mul_assoc, ← mul_pow, add_mul, one_mul, div_mul_cancel₀ y hx0]
    rw [e]
    exact Oc.mul_mem (Oc.pow_mem (Oc.add_mem Oc.one_mem h) b) (hx a b hb hab)

variable (p Oc) in

def MG (hval : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc) (g : ℝ) : AddSubgroup Kc where
  carrier := {x | geX p Oc x g}
  add_mem' := fun hx hy => geX_add hval hx hy
  zero_mem' := geX_zero g
  neg_mem' := fun hx => geX_neg hx

end Formalism.L2.PairingIndexBounds.Ent
