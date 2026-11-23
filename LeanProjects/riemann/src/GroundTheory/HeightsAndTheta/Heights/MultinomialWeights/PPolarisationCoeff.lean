import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem PolarisationCoeff.prod_X_pow_eq_monomial_one {σ S : Type*} [CommSemiring S] [Fintype σ] (K : σ →₀ ℕ) :
    ∏ v, (X v : MvPolynomial σ S) ^ K v = monomial K 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem PolarisationCoeff.coeff_polarPoly {σ R : Type*} [CommRing R] [Fintype σ]
    (Φ : MvPolynomial σ R →ₗ[R] R) (n : ℕ) (m : σ →₀ ℕ) :
    coeff m (polarPoly Φ n) = Φ (coeff m ((-outerDot σ R) ^ n)) := by
  classical
  unfold polarPoly
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

theorem PolarisationCoeff.coeff_outerDot_pow {σ R : Type*} [CommRing R] [Fintype σ] (n : ℕ) (m : σ →₀ ℕ)
    (hm : (m.sum fun _ e => e) = n) :
    coeff m ((outerDot σ R) ^ n) = (Nat.multinomial univ m : MvPolynomial σ R) * monomial m 1 := by
  classical
  unfold outerDot
  rw [Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  have hterm : ∀ k : σ → ℕ,
      (Nat.multinomial univ k : MvPolynomial σ (MvPolynomial σ R)) *
          ∏ v, (X v * C (X v) : MvPolynomial σ (MvPolynomial σ R)) ^ k v =
        monomial (Finsupp.equivFunOnFinite.symm k)
          ((Nat.multinomial univ k : MvPolynomial σ R) *
            monomial (Finsupp.equivFunOnFinite.symm k) 1) := by
    intro k
    simp_rw [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    have h1 := PolarisationCoeff.prod_X_pow_eq_monomial_one (S := MvPolynomial σ R) (Finsupp.equivFunOnFinite.symm k)
    have h2 := PolarisationCoeff.prod_X_pow_eq_monomial_one (S := R) (Finsupp.equivFunOnFinite.symm k)
    simp only [Finsupp.coe_equivFunOnFinite_symm] at h1 h2
    rw [h1, h2, ← map_natCast (C : MvPolynomial σ R →+* _),
      mul_comm (monomial _ (1 : MvPolynomial σ R)) (C _), C_mul_monomial, mul_one, C_mul_monomial]
  simp_rw [hterm, coeff_monomial]
  have hiff : ∀ k : σ → ℕ, Finsupp.equivFunOnFinite.symm k = m ↔ (⇑m : σ → ℕ) = k := by
    intro k
    constructor
    · rintro rfl; rfl
    · rintro rfl; exact Finsupp.equivFunOnFinite.symm_apply_apply m
  simp_rw [hiff]
  rw [Finset.sum_ite_eq]
  have hmem : (⇑m : σ → ℕ) ∈ piAntidiag univ n := by
    rw [mem_piAntidiag]
    refine ⟨?_, fun i _ => mem_univ i⟩
    rw [← hm, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  rw [if_pos hmem, Finsupp.equivFunOnFinite_symm_coe]

theorem PolarisationCoeff.proof : PolarisationCoeff.Statement := by
  intro σ _ Φ n m hm
  classical
  have hneg : ((-1 : MvPolynomial σ (MvPolynomial σ ℝ)) ^ n) = C ((-1 : MvPolynomial σ ℝ) ^ n) := by
    simp
  rw [PolarisationCoeff.coeff_polarPoly, neg_pow (outerDot σ ℝ), hneg, coeff_C_mul,
    PolarisationCoeff.coeff_outerDot_pow n m hm]
  have hsmul : (-1 : MvPolynomial σ ℝ) ^ n * ((Nat.multinomial univ m : MvPolynomial σ ℝ) * monomial m 1) =
      ((-1 : ℝ) ^ n * (Nat.multinomial univ m : ℝ)) • monomial m 1 := by
    rw [smul_eq_C_mul, C_mul, C_pow, C_neg, C_1, map_natCast (C : ℝ →+* MvPolynomial σ ℝ), mul_assoc]
  rw [hsmul, map_smul, smul_eq_mul]
  have hsum : ∑ v, m v = n := by rw [← hm, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  have hprod : (m.prod fun _ e => (e.factorial : ℝ)) * (Nat.multinomial univ m : ℝ) = (n.factorial : ℝ) := by
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp), ← hsum]
    exact_mod_cast Nat.multinomial_spec univ m
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hsq : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by rw [← mul_pow]; simp
  calc Φ (monomial m 1)
      = ((-1 : ℝ) ^ n * (-1) ^ n) * (((m.prod fun _ e => (e.factorial : ℝ)) *
          (Nat.multinomial univ m : ℝ)) / (n.factorial : ℝ)) * Φ (monomial m 1) := by
        rw [hsq, hprod, div_self hn, one_mul, one_mul]
    _ = _ := by ring

end GroundTheory.Heights₂.Heights.TheoremB
