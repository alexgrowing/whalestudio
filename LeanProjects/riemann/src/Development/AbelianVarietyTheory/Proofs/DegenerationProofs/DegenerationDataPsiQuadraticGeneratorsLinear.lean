import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.PsiQuadratic
variable {O : Type} [CommRing O] (N : NumD O)

theorem τ_self (y : N.X) : N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) := by
  have a := N.τ_add_left y (-y) y
  rw [add_neg_cancel, N.τ_zero_left, one_mul, N.c_neg] at a
  have b := N.ψ_add (-y) y
  rw [neg_add_cancel, N.ψ_zero] at b
  have a' := congrArg Additive.ofMul a
  have b' := congrArg Additive.ofMul b
  have c' := congrArg Additive.ofMul (N.even y)
  apply Additive.ofMul.injective
  simp only [dbl, sq, ofMul_mul, ofMul_div, ofMul_one] at a' b' c' ⊢
  linear_combination (norm := abel) -a' + b' + c'

theorem s_nsmul (g : N.Gt) (n : ℕ) (y : N.X) : g.s (n • y) * cubN N.θ n 1 (N.c y) g.b = g.s y ^ n := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have m := g.mult (n • y) y
    rw [N.c_nsmul] at m
    rw [cubN] at ih
    rw [succ_nsmul, cubN, Finset.prod_range_succ, one_mul, pow_succ, ← ih, mul_right_comm _ _ (g.s y), ← m,
      ← mul_assoc, mul_right_comm]

theorem ψ_nsmul (n : ℕ) (y : N.X) : N.ψ (n • y) * mulq N.θ N.σ n (N.c y) = N.ψ y ^ (n ^ 2) := by
  induction n with
  | zero => simp [mulq]
  | succ n ih =>
    have a := s_nsmul N (N.io y) n y
    rw [N.io_s, N.io_s, N.io_b, τ_self, N.τ_symm] at a
    rw [mulq] at ih
    rw [succ_nsmul, N.ψ_add, mulq, Finset.prod_range_succ, show (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 by ring,
      pow_succ, pow_add, pow_mul, ← ih]
    rw [mul_pow] at a
    have a' := congrArg Additive.ofMul a
    apply Additive.ofMul.injective
    generalize (N.ψ y ^ 2) ^ n = u at a' ⊢
    generalize dbl N.θ N.σ (N.c y) ^ n = v at a' ⊢
    simp only [ofMul_mul, ofMul_div] at a' ⊢
    linear_combination (norm := abel) a'

theorem main : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n : ℕ) (y : N.X),
    N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) ∧ N.ψ (n • y) * mulq N.θ N.σ n (N.c y) = N.ψ y ^ (n ^ 2) ∧
    ∀ (g : N.Gt), g.s (n • y) * cubN N.θ n 1 (N.c y) g.b = g.s y ^ n ∧
      (g ^ n).s y * cubN N.θ n 1 g.b (N.c y) = g.s y ^ n :=
  fun _ _ N n y => ⟨τ_self N y, ψ_nsmul N n y, fun g => ⟨s_nsmul N g n y, g.pow_s n y⟩⟩

end GlobalTheory.PsiQuadratic
