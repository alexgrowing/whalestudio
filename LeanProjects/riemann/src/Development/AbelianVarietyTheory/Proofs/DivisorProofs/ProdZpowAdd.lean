import Mathlib

namespace GlobalTheory.ProductZpowAdd

theorem prod_zpow_add {F : Type} [inst : Field F] {d : ℕ} (x : Fin (d + 1) → F)
    (hx : ∀ i : Fin (d + 1), x i ≠ 0) (m n : Fin (d + 1) → ℤ) :
    ∏ j : Fin (d + 1), x j ^ (m j + n j)
      = (∏ j : Fin (d + 1), x j ^ m j) * ∏ j : Fin (d + 1), x j ^ n j := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => zpow_add₀ (hx j) _ _

end GlobalTheory.ProductZpowAdd
