import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
open MvPolynomial GlobalTheory.ArInt GlobalTheory.Mean4O
open scoped Classical

namespace GlobalTheory.IntRealPow

theorem exists_poly_eval {ι : Type} [Fintype ι] (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ) (e : ℕ) :
    ∀ P : MvPolynomial (Option ι) ℝ, ∃ Q : MvPolynomial ι ℝ, ∀ β : ι → ℝ,
      Φ (P * rename some (lin β) ^ e) = eval β Q := by
  induction e with
  | zero => intro P; exact ⟨C (Φ P), fun β => by simp⟩
  | succ e ih =>
    intro P
    choose Q hQ using ih
    refine ⟨∑ i, X i * Q (P * X (some i)), fun β => ?_⟩
    have h : P * rename some (lin β) ^ (e + 1)
        = ∑ i, β i • (P * X (some i) * rename some (lin β) ^ e) := by
      rw [pow_succ']
      generalize rename some (lin β) ^ e = R
      unfold lin
      rw [map_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, rename_C, rename_X, smul_eq_C_mul]
      ring
    rw [h, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hQ, map_mul, eval_X, smul_eq_mul]

theorem vanish_real_of_vanish_int {ι : Type} [Fintype ι]
    (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ) (P : MvPolynomial (Option ι) ℝ) (e : ℕ)
    (h : ∀ n : ι → ℤ, Φ (P * rename some (lin fun i => (n i : ℝ)) ^ e) = 0) (β : ι → ℝ) :
    Φ (P * rename some (lin β) ^ e) = 0 := by
  obtain ⟨Q, hQ⟩ := exists_poly_eval Φ e P
  have hQ0 : Q = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun x hx => ?_
    have hx' : ∀ i, ∃ n : ℤ, (n : ℝ) = x i := fun i => hx i (Set.mem_univ i)
    choose n hn using hx'
    have hxn : x = fun i => (n i : ℝ) := funext fun i => (hn i).symm
    rw [← hQ, hxn, h, map_zero]
  rw [hQ, hQ0, map_zero]

end GlobalTheory.IntRealPow
