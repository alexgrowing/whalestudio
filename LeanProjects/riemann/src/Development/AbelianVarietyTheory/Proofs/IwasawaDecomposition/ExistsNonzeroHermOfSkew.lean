import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem exists_herm_mulVec_self_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (G : Matrix (Fin N) (Fin N) E) (κ : E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → cc κ = -κ →
    κ ≠ 0 → ∀ n : Matrix (Fin N) (Fin N) E, IsSkew G n → n ≠ 0 → ∃ x, herm G (n.mulVec x) x ≠ 0 := by
  intro E _ _ _ N G κ _ hdet hκ hκ0 n _ hn
  by_contra hcon
  push_neg at hcon
  have pol : ∀ x y, herm G (n.mulVec x) y + herm G (n.mulVec y) x = 0 := by
    intro x y
    have h := hcon (x + y)
    rw [Matrix.mulVec_add, herm_add_left, herm_add_right, herm_add_right, hcon x, hcon y] at h
    linear_combination h
  have key : ∀ x y, herm G (n.mulVec x) y = 0 := by
    intro x y
    have h1 := pol (κ • x) y
    rw [Matrix.mulVec_smul, herm_smul_left, herm_smul_right, hκ] at h1
    have h2 := pol x y
    have h3 : (2 * κ) * herm G (n.mulVec x) y = 0 := by linear_combination h1 + κ * h2
    have h4 : (2 * κ : E) ≠ 0 := mul_ne_zero two_ne_zero hκ0
    exact (mul_eq_zero.1 h3).resolve_left h4
  apply hn
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [Matrix.zero_mulVec]
  exact eq_zero_of_herm G hdet _ (key x)

end GlobalTheory.UnipKill
