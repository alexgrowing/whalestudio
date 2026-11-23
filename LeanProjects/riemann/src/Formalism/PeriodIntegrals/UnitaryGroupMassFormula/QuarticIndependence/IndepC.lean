import Mathlib

namespace PI.QmIndepW

open Complex

theorem quartic_coeffs (a0 a1 a2 a3 a4 : ℂ)
    (h : ∀ t : ℕ, 1 ≤ t → t ≤ 5 → a0 + a1 * t + a2 * (t : ℂ) ^ 2 + a3 * (t : ℂ) ^ 3 + a4 * (t : ℂ) ^ 4 = 0) :
    a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 0 := by
  have h1 := h 1 le_rfl (by norm_num)
  have h2 := h 2 (by norm_num) (by norm_num)
  have h3 := h 3 (by norm_num) (by norm_num)
  have h4 := h 4 (by norm_num) (by norm_num)
  have h5 := h 5 (by norm_num) le_rfl
  push_cast at h1 h2 h3 h4 h5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination 5 * h1 - 10 * h2 + 10 * h3 - 5 * h4 + h5
  · linear_combination (-77/12 : ℂ) * h1 + (107/6 : ℂ) * h2 + (-39/2 : ℂ) * h3 + (61/6 : ℂ) * h4 + (-25/12 : ℂ) * h5
  · linear_combination (71/24 : ℂ) * h1 + (-59/6 : ℂ) * h2 + (49/4 : ℂ) * h3 + (-41/6 : ℂ) * h4 + (35/24 : ℂ) * h5
  · linear_combination (-7/12 : ℂ) * h1 + (13/6 : ℂ) * h2 + (-3 : ℂ) * h3 + (11/6 : ℂ) * h4 + (-5/12 : ℂ) * h5
  · linear_combination (1/24 : ℂ) * h1 + (-1/6 : ℂ) * h2 + (1/4 : ℂ) * h3 + (-1/6 : ℂ) * h4 + (1/24 : ℂ) * h5

def nine (u v y00 y10 y20 y01 y11 y21 y02 y12 y22 : ℂ) : ℂ :=
  y00 + u * y10 + u ^ 2 * y20 + v * y01 + u * v * y11 + u ^ 2 * v * y21 + v ^ 2 * y02 + u * v ^ 2 * y12 +
    u ^ 2 * v ^ 2 * y22

def IndepC : Prop :=
  ∀ y00 y10 y20 y01 y11 y21 y02 y12 y22 : ℂ,
    (∀ c : ℂ, c ≠ 0 → nine c⁻¹ (star c)⁻¹ y00 y10 y20 y01 y11 y21 y02 y12 y22 = 0) →
    y00 = 0 ∧ y10 = 0 ∧ y20 = 0 ∧ y01 = 0 ∧ y11 = 0 ∧ y21 = 0 ∧ y02 = 0 ∧ y12 = 0 ∧ y22 = 0

theorem ray (y00 y10 y20 y01 y11 y21 y02 y12 y22 : ℂ)
    (hyp : ∀ c : ℂ, c ≠ 0 → nine c⁻¹ (star c)⁻¹ y00 y10 y20 y01 y11 y21 y02 y12 y22 = 0)
    (ω ω' : ℂ) (hω : ω ≠ 0) (hs : star ω = ω') :
    y00 = 0 ∧ ω * y10 + ω' * y01 = 0 ∧ ω ^ 2 * y20 + ω * ω' * y11 + ω' ^ 2 * y02 = 0 ∧
      ω ^ 2 * ω' * y21 + ω * ω' ^ 2 * y12 = 0 ∧ ω ^ 2 * ω' ^ 2 * y22 = 0 := by
  refine quartic_coeffs _ _ _ _ _ fun t ht1 _ => ?_
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h := hyp _ (inv_ne_zero (mul_ne_zero ht hω))
  simp only [inv_inv, star_inv₀, star_mul', star_natCast, hs, nine] at h
  linear_combination h

theorem indepC : IndepC := by
  intro y00 y10 y20 y01 y11 y21 y02 y12 y22 hyp
  obtain ⟨A1, B1, C1, D1, E1⟩ := ray _ _ _ _ _ _ _ _ _ hyp 1 1 one_ne_zero (by simp)
  obtain ⟨-, B2, C2, D2, -⟩ := ray _ _ _ _ _ _ _ _ _ hyp I (-I) I_ne_zero (by simp)
  obtain ⟨-, -, C3, -, -⟩ := ray _ _ _ _ _ _ _ _ _ hyp (1 + I) (1 - I)
    (by intro h; have := congrArg Complex.re h; simp at this) (by simp [sub_eq_add_neg])
  have h2I : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  have h4I : (4 : ℂ) * I ≠ 0 := mul_ne_zero (by norm_num) I_ne_zero
  have y01z : y01 = 0 := by
    have : (2 * I) * y01 = 0 := by linear_combination I * B1 - B2
    exact (mul_eq_zero.mp this).resolve_left h2I
  have y10z : y10 = 0 := by linear_combination B1 - y01z
  have y12z : y12 = 0 := by
    have : (2 * I) * y12 = 0 := by linear_combination I * D1 - D2 + (I * y12 - I * y21) * I_sq
    exact (mul_eq_zero.mp this).resolve_left h2I
  have y21z : y21 = 0 := by linear_combination D1 - y12z
  have y11z : y11 = 0 := by
    have : (2 : ℂ) * y11 = 0 := by linear_combination C1 + C2 + (y11 - y20 - y02) * I_sq
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  have y20z : y20 = 0 := by
    have : (4 * I) * y20 = 0 := by
      linear_combination C3 - (y20 - y11 + y02) * I_sq + 2 * I * C1 - (2 + 2 * I) * y11z
    exact (mul_eq_zero.mp this).resolve_left h4I
  have y02z : y02 = 0 := by linear_combination C1 - y11z - y20z
  have y22z : y22 = 0 := by linear_combination E1
  exact ⟨A1, y10z, y20z, y01z, y11z, y21z, y02z, y12z, y22z⟩

end PI.QmIndepW
