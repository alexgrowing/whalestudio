import Mathlib

namespace GlobalTheory.CommuteInvLeft

theorem commute_inv_left : ∀ {B : Type} [inst : Ring B] {x xi y : B},
    x * xi = (1 : B) → xi * x = (1 : B) → Commute x y → Commute xi y := by
  intro B _ x xi y h1 h2 h
  have h' : x * y = y * x := h
  show xi * y = y * xi
  calc xi * y = xi * y * (x * xi) := by rw [h1, mul_one]
    _ = xi * (y * x) * xi := by simp only [mul_assoc]
    _ = xi * (x * y) * xi := by rw [h']
    _ = (xi * x) * y * xi := by simp only [mul_assoc]
    _ = y * xi := by rw [h2, one_mul]

end GlobalTheory.CommuteInvLeft
