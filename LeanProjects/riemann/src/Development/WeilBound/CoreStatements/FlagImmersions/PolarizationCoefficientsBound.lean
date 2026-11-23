import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem pa_neg_lin_pow {J : Type} [Fintype J] [DecidableEq J] (d : ℕ) (c : J → ℝ) :
    ((-∑ x, C (c x) * X x : MvPolynomial J ℝ)) ^ d =
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset J) d,
        ((-1) ^ d * (m.multinomial : ℝ) * m.prod (fun r e => c r ^ e)) • monomial m (1 : ℝ) := by
  rw [neg_pow, Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
  refine Finset.sum_nbij' (fun g => Finsupp.equivFunOnFinite.symm g) (fun m => ⇑m) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_piAntidiag] at hg
    simp only [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    simpa using hg.1
  · intro m hm
    simp only [Finset.mem_finsuppAntidiag] at hm
    simp only [Finset.mem_piAntidiag]
    exact ⟨hm.1, fun i _ => Finset.mem_univ i⟩
  · intro g _
    simp
  · intro m _
    simp
  · intro g _
    set m : J →₀ ℕ := Finsupp.equivFunOnFinite.symm g with hm
    have hg : g = ⇑m := by simp [hm]
    rw [hg, Finsupp.multinomial_of_support_subset (Finset.subset_univ _),
      Finsupp.prod_fintype _ _ (by simp), monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    simp only [mul_pow, Finset.prod_mul_distrib, smul_eq_C_mul, map_mul, map_prod, map_pow, map_natCast,
      map_neg, map_one]
    ring

theorem polarization_coefficients_bound : ∀ (J : Type) [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ), ∃ Pl : MvPolynomial J ℝ, Pl.IsHomogeneous d ∧ (∀ c : J → ℝ, eval c Pl = Φ ((-∑ x, C (c x) * X x) ^ d)) ∧ (∀ m : J →₀ ℕ, m.degree = d → coeff m Pl = (-1) ^ d * (m.multinomial : ℝ) * Φ (monomial m 1)) ∧ ∀ m : J →₀ ℕ, m.degree = d → |Φ (monomial m 1)| ≤ |coeff m Pl| := by
  intro J _ _ d Φ
  set S := Finset.finsuppAntidiag (Finset.univ : Finset J) d with hSdef
  have hS : ∀ m : J →₀ ℕ, m ∈ S ↔ m.degree = d := by
    intro m
    simp [hSdef, Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  set a : (J →₀ ℕ) → ℝ := fun m => (-1) ^ d * (m.multinomial : ℝ) * Φ (monomial m 1) with ha
  set Pl : MvPolynomial J ℝ := ∑ m ∈ S, monomial m (a m) with hPl
  have hcoeff : ∀ m : J →₀ ℕ, m.degree = d → coeff m Pl = a m := by
    intro m hm
    rw [hPl, coeff_sum, Finset.sum_eq_single m]
    · simp
    · intro b _ hb
      rw [coeff_monomial, if_neg hb]
    · intro hm'
      exact absurd ((hS m).2 hm) hm'
  refine ⟨Pl, ?_, ?_, hcoeff, ?_⟩
  · apply IsHomogeneous.sum
    intro m hm
    exact isHomogeneous_monomial _ ((hS m).1 hm)
  · intro c
    rw [pa_neg_lin_pow, hPl, map_sum (eval c), map_sum Φ]
    refine Finset.sum_congr hSdef fun m _ => ?_
    rw [eval_monomial, map_smul, smul_eq_mul, ha]
    ring
  · intro m hm
    rw [hcoeff m hm, ha]
    have hpos : (1 : ℝ) ≤ (m.multinomial : ℝ) := by
      have : 0 < m.multinomial := by
        rw [Finsupp.multinomial_eq]
        exact Nat.multinomial_pos _ _
      exact_mod_cast this
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    nlinarith [abs_nonneg (Φ (monomial m 1))]

end RootFieldNumerics
