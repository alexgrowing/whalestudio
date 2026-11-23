import Mathlib
open MvPolynomial

namespace GlobalTheory

theorem coeff_eval₂_C_mul_X {F K : Type} [Field F] [Field K] (φ : F →+* K) {r : ℕ} (w : Fin r → K)
    (p : MvPolynomial (Fin r) F) (d : ℕ) :
    (MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) p).coeff d
      = MvPolynomial.eval₂ φ w (homogeneousComponent d p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    have hprod : (u.prod fun i k => (Polynomial.C (w i) * Polynomial.X : Polynomial K) ^ k)
        = Polynomial.C (u.prod fun i k => w i ^ k) * Polynomial.X ^ (Finsupp.degree u) := by
      simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow,
        Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
    have hcomp : homogeneousComponent d (monomial u a)
        = if Finsupp.degree u = d then monomial u a else 0 := by
      ext v
      rw [coeff_homogeneousComponent]
      by_cases hd : Finsupp.degree u = d
      · by_cases hv : u = v
        · subst hv; simp [hd]
        · simp [coeff_monomial, hv, hd]
      · by_cases hv : u = v
        · subst hv; simp [hd]
        · simp [coeff_monomial, hv, hd]
    rw [eval₂_monomial, hprod, hcomp, ← mul_assoc, RingHom.comp_apply, ← map_mul,
      Polynomial.coeff_C_mul_X_pow]
    by_cases h : Finsupp.degree u = d
    · subst h
      simp [eval₂_monomial]
    · have h' : d ≠ Finsupp.degree u := fun e => h e.symm
      simp [h, h']
  | add p q hp hq =>
    simp only [eval₂_add, Polynomial.coeff_add, map_add, hp, hq]

theorem homogeneous_components_of_integral_equation (F K : Type) [Field F] [Field K] (φ : F →+* K)
    (r e m : ℕ) (w : Fin r → K) (τ : K) (b : Fin m → MvPolynomial (Fin r) F)
    (h : (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ)
      (fun i => Polynomial.C (w i) * Polynomial.X) (b k) *
        (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0) :
    ∃ a : Fin m → MvPolynomial (Fin r) F, (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧
      τ ^ m + ∑ k, MvPolynomial.eval₂ φ w (a k) * τ ^ (k : ℕ) = 0 := by
  refine ⟨fun k => homogeneousComponent (e * (m - k)) (b k),
    fun k => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have hc := congrArg (fun P : Polynomial K => P.coeff (e * m)) h
  simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hc
  have hpow : ∀ n : ℕ, (Polynomial.C τ * Polynomial.X ^ e) ^ n
      = Polynomial.C (τ ^ n) * Polynomial.X ^ (e * n) := by
    intro n
    rw [mul_pow, ← pow_mul, map_pow]
  have hterm : ∀ k : Fin m, (MvPolynomial.eval₂ (Polynomial.C.comp φ)
      (fun i => Polynomial.C (w i) * Polynomial.X) (b k) *
        (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ)).coeff (e * m)
      = MvPolynomial.eval₂ φ w (homogeneousComponent (e * (m - k)) (b k)) * τ ^ (k : ℕ) := by
    intro k
    have hle : e * (k : ℕ) ≤ e * m := Nat.mul_le_mul_left e k.is_lt.le
    rw [hpow, ← mul_assoc, Polynomial.coeff_mul_X_pow', if_pos hle, Polynomial.coeff_mul_C,
      ← Nat.mul_sub, coeff_eval₂_C_mul_X]
  rw [hpow, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at hc
  simpa only [hterm] using hc

end GlobalTheory
