import Mathlib

noncomputable section

open MvPolynomial

namespace PI.FJMB

variable {R : Type*} [CommRing R] {σ : Type*}

private theorem sum_aeval_pderiv_X_mul_derivation {B : Type*} [CommRing B] [Algebra R B] (D : Derivation R B B)
    (φ : σ → B) (S : Finset σ) (hS : ∀ v, v ∉ S → D (φ v) = 0) (w : σ) :
    ∑ v ∈ S, aeval φ (pderiv v (X w : MvPolynomial σ R)) * D (φ v) = D (φ w) := by
  classical
  have key : ∀ v, aeval φ (pderiv v (X w : MvPolynomial σ R)) * D (φ v) =
      if w = v then D (φ v) else 0 := by
    intro v
    rw [pderiv_X]
    by_cases h : w = v
    · subst h
      simp
    · simp [Pi.single_apply, h]
  rw [Finset.sum_congr rfl (fun v _ => key v), Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (hS w h).symm

theorem deriv_aeval {B : Type*} [CommRing B] [Algebra R B] (D : Derivation R B B) (φ : σ → B)
    (S : Finset σ) (hS : ∀ v, v ∉ S → D (φ v) = 0) (f : MvPolynomial σ R) :
    D (aeval φ f) = ∑ v ∈ S, aeval φ (pderiv v f) * D (φ v) := by
  classical
  induction f using MvPolynomial.induction_on
  · rename_i a
    simp [aeval_C]
  · rename_i p q hp hq
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  · rename_i p w hp
    have h1 : ∀ v, pderiv v (p * X w) = pderiv v p * X w + p * pderiv v (X w) := by
      intro v
      simp only [Derivation.leibniz, smul_eq_mul]
      ring
    simp only [h1, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib]
    have h2 : ∑ v ∈ S, aeval φ p * aeval φ (pderiv v (X w : MvPolynomial σ R)) * D (φ v) =
        aeval φ p * D (φ w) := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, sum_aeval_pderiv_X_mul_derivation D φ S hS w]
    have h3 : ∑ v ∈ S, aeval φ (pderiv v p) * φ w * D (φ v) =
        φ w * ∑ v ∈ S, aeval φ (pderiv v p) * D (φ v) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, h2, h3, ← hp]
    ring

theorem aeval_translate_eq {K : Type*} [Field K] [CharZero K] [Algebra R K] (f : MvPolynomial σ R)
    (S : Finset σ) (c : σ → MvPolynomial σ R) (hf : ∑ v ∈ S, c v * pderiv v f = 0) (y z : σ → K)
    (hz : ∀ v, v ∉ S → z v = 0)
    (hc : ∀ v ∈ S, aeval (fun w => Polynomial.C (y w) + Polynomial.X * Polynomial.C (z w)) (c v) =
      Polynomial.C (z v)) (t : K) :
    aeval (fun w => y w + t * z w) f = aeval y f := by
  classical
  set φ : σ → Polynomial K := fun w => Polynomial.C (y w) + Polynomial.X * Polynomial.C (z w)
    with hφ
  let D : Derivation R (Polynomial K) (Polynomial K) :=
    (Polynomial.derivative' : Derivation K (Polynomial K) (Polynomial K)).restrictScalars R
  have hD : ∀ q, D q = Polynomial.derivative q := fun q => rfl
  have hDφ : ∀ v, D (φ v) = Polynomial.C (z v) := by
    intro v
    rw [hD, hφ]
    simp
  have hS : ∀ v, v ∉ S → D (φ v) = 0 := by
    intro v hv
    rw [hDφ, hz v hv, map_zero]
  have hder : Polynomial.derivative (aeval φ f) = 0 := by
    rw [← hD, deriv_aeval D φ S hS f]
    calc ∑ v ∈ S, aeval φ (pderiv v f) * D (φ v) = ∑ v ∈ S, aeval φ (c v * pderiv v f) := by
          refine Finset.sum_congr rfl (fun v hv => ?_)
          rw [hDφ, map_mul, ← hc v hv, mul_comm]
      _ = aeval φ (∑ v ∈ S, c v * pderiv v f) := by rw [map_sum]
      _ = 0 := by rw [hf, map_zero]
  have hconst : aeval φ f = Polynomial.C ((aeval φ f).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_derivative_eq_zero hder)
  have heval : ∀ (s : K) (g : MvPolynomial σ R),
      (aeval φ g).eval s = aeval (fun w => y w + s * z w) g := by
    intro s g
    induction g using MvPolynomial.induction_on
    · rename_i a
      simp [aeval_C, Polynomial.algebraMap_apply]
    · rename_i p q hp hq
      simp only [map_add, Polynomial.eval_add, hp, hq]
    · rename_i p n hp
      rw [map_mul, aeval_X, Polynomial.eval_mul, hp, map_mul, aeval_X]
      congr 1
      simp only [hφ, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  have h0 : (aeval φ f).eval 0 = aeval y f := by
    have hy : (fun w => y w + 0 * z w) = y := by
      funext w
      simp
    rw [heval 0 f, hy]
  rw [← heval t f, ← h0, hconst, Polynomial.eval_C, Polynomial.eval_C]

end PI.FJMB
