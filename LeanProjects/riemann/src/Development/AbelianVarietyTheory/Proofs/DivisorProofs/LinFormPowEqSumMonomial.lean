import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly

theorem linForm_pow_eq_sum_monomial {σ : Type} [Fintype σ] [DecidableEq σ] (a : σ → ℝ) (d : ℕ) :
    (∑ x : σ, a x • (X x : MvPolynomial σ ℝ)) ^ d =
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset σ) d,
        ((Nat.multinomial Finset.univ m : ℝ) * ∏ x, a x ^ m x) • (monomial m 1 : MvPolynomial σ ℝ) := by
  ext s
  rw [coeff_linearCombination_X_pow_of_fintype, coeff_sum]
  simp only [coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq', Finsupp.sum_fintype _ _ (fun _ => rfl),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  simp [Finset.mem_finsuppAntidiag]

theorem coeff_eq_of_polarisation : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (d : ℕ) (Φ : Pol ι N →ₗ[ℝ] ℝ) (P : Pol ι N), (∀ lam : ι → Fin N → ℝ, ev lam P = Φ (linRoot lam ^ d)) → ∀ m : (ι × Fin N) →₀ ℕ, m.degree = d → P.coeff m = (-1) ^ d * (Nat.multinomial Finset.univ m : ℝ) * Φ (monomial m 1) ∧ |Φ (monomial m 1)| ≤ |P.coeff m| := by
  intro ι _ _ N d Φ P h m hm
  have hP : P = ∑ k ∈ Finset.finsuppAntidiag (Finset.univ : Finset (ι × Fin N)) d,
      monomial k ((-1) ^ d * (Nat.multinomial Finset.univ k : ℝ) * Φ (monomial k 1)) := by
    apply MvPolynomial.funext
    intro x
    have h1 := h (fun τ i => x (τ, i))
    have hl : linRoot (fun τ i => x (τ, i)) =
        -∑ y : ι × Fin N, x y • (X y : MvPolynomial (ι × Fin N) ℝ) := by
      simp [linRoot, smul_eq_C_mul]
    have h2 : ev (fun τ i => x (τ, i)) P = eval x P := rfl
    have h3 : ((-1 : MvPolynomial (ι × Fin N) ℝ)) ^ d = C ((-1 : ℝ) ^ d) := by simp
    rw [← h2, h1, hl, neg_pow, h3, ← smul_eq_C_mul, linForm_pow_eq_sum_monomial, map_smul, map_sum, map_sum,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), smul_eq_mul]
    ring
  have hmem : m ∈ Finset.finsuppAntidiag (Finset.univ : Finset (ι × Fin N)) d := by
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨by rw [← hm, Finsupp.degree_eq_sum], Finset.subset_univ _⟩
  have hc : P.coeff m = (-1) ^ d * (Nat.multinomial Finset.univ m : ℝ) * Φ (monomial m 1) := by
    rw [hP, coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq', if_pos hmem]
  refine ⟨hc, ?_⟩
  rw [hc, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  have : (1 : ℝ) ≤ (Nat.multinomial Finset.univ m : ℝ) := by
    exact_mod_cast Nat.multinomial_pos Finset.univ m
  exact le_mul_of_one_le_left (abs_nonneg _) this

end GlobalTheory.FlagPoly
