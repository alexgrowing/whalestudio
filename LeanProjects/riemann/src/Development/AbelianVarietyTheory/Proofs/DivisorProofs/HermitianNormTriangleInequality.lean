import Mathlib
open MeasureTheory
open scoped ComplexOrder

namespace GlobalTheory

theorem posDef_herm_norm_triangle :
    ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), Hm.PosDef →
      √(((a + b) ⬝ᵥ Hm.mulVec (star (a + b))).re) ≤
        √((a ⬝ᵥ Hm.mulVec (star a)).re) + √((b ⬝ᵥ Hm.mulVec (star b)).re) := by
  intro g Hm a b hH
  have hS := hH.posSemidef
  have key : ∀ x : Fin g → ℂ,
      @norm _ (Hm.toSeminormedAddCommGroup hS).toNorm (star x) = √((x ⬝ᵥ Hm.mulVec (star x)).re) := by
    intro x
    rw [@norm_eq_sqrt_re_inner ℂ _ _ (Hm.toSeminormedAddCommGroup hS) (Hm.toInnerProductSpace hS)]
    change √(RCLike.re ((Hm.mulVec (star x)) ⬝ᵥ star (star x))) = _
    rw [star_star, dotProduct_comm, RCLike.re_to_complex]
  have h := @norm_add_le _ (Hm.toSeminormedAddCommGroup hS).toSeminormedAddGroup (star a) (star b)
  rw [← star_add, key, key, key] at h
  exact h

end GlobalTheory
