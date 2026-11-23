import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial Finset

theorem PolarisationDegreeD.proof : PolarisationDegreeD.Statement := by
  intro K _ _ r D φ ψ h P hP
  set χ : MvPolynomial (Fin r) K →ₗ[K] K := φ - ψ with hχdef
  have hχ : ∀ c : Fin r → K, χ ((∑ i, C (c i) * X i) ^ D) = 0 := fun c => by
    simp [hχdef, h c]

  have hmono : ∀ k : Fin r → ℕ, (∏ i, X i ^ k i : MvPolynomial (Fin r) K) =
      monomial (Finsupp.equivFunOnFinite.symm k) 1 := by
    intro k
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp

  have hexp : ∀ c : Fin r → K, (∑ i, C (c i) * X i : MvPolynomial (Fin r) K) ^ D =
      ∑ k ∈ piAntidiag univ D,
        C ((Nat.multinomial univ k : K) * ∏ i, c i ^ k i) * ∏ i, X i ^ k i := by
    intro c
    rw [sum_pow_eq_sum_piAntidiag]
    refine sum_congr rfl fun k _ => ?_
    simp only [mul_pow, prod_mul_distrib, map_mul, map_prod, map_pow, map_natCast]
    ring

  set Q : MvPolynomial (Fin r) K := ∑ k ∈ piAntidiag univ D,
      C ((Nat.multinomial univ k : K) * χ (∏ i, X i ^ k i)) * ∏ i, X i ^ k i with hQdef
  have hQ : Q = 0 := by
    apply MvPolynomial.funext
    intro c
    rw [map_zero, ← hχ c, hexp c, hQdef, map_sum, map_sum]
    refine sum_congr rfl fun k _ => ?_
    have hs : C ((Nat.multinomial univ k : K) * ∏ i, c i ^ k i) * ∏ i, X i ^ k i =
        ((Nat.multinomial univ k : K) * ∏ i, c i ^ k i) • (∏ i, X i ^ k i : MvPolynomial (Fin r) K) :=
      C_mul'
    rw [hs, map_smul, smul_eq_mul, eval_mul, eval_C]
    simp only [map_prod, map_pow, eval_X]
    ring

  have hzero : ∀ k ∈ piAntidiag univ D, χ (∏ i, X i ^ k i) = 0 := by
    intro k hk
    have hc : coeff (Finsupp.equivFunOnFinite.symm k) Q =
        (Nat.multinomial univ k : K) * χ (∏ i, X i ^ k i) := by
      rw [hQdef, coeff_sum]
      simp_rw [hmono, coeff_C_mul, coeff_monomial, EmbeddingLike.apply_eq_iff_eq]
      simp [hk]
    rw [hQ, coeff_zero] at hc
    have hm : (Nat.multinomial univ k : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.multinomial_pos _ _).ne'
    exact (mul_eq_zero.mp hc.symm).resolve_left hm

  have hP0 : χ P = 0 := by
    rw [as_sum P, map_sum]
    refine sum_eq_zero fun d hd => ?_
    have hdeg : ∑ i, d i = D := by
      rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
      exact hP (mem_support_iff.mp hd)
    have hmem : (⇑d : Fin r → ℕ) ∈ piAntidiag univ D := by
      simp [hdeg]
    have hd1 : monomial d (coeff d P) = coeff d P • monomial d (1 : K) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hd1, map_smul, smul_eq_mul]
    have := hzero _ hmem
    rw [hmono, Finsupp.equivFunOnFinite_symm_coe] at this
    rw [this, mul_zero]
  have := hP0
  rw [hχdef, LinearMap.sub_apply, sub_eq_zero] at this
  exact this

end GroundTheory.Heights₂.Heights.FlagBundles
