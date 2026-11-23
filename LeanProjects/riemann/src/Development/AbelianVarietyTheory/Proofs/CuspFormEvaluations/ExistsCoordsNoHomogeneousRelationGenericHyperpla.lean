import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsAlgebraicIndependentRatiosOfGenericZero

namespace GlobalTheory

open MvPolynomial in

theorem aeval_mul_of_isHomogeneous_cone {K L ι : Type} [CommRing K] [CommRing L] [Algebra K L]
    {Q : MvPolynomial ι K} {d : ℕ} (hQ : Q.IsHomogeneous d) (c : L) (x : ι → L) :
    aeval (fun a => c * x a) Q = c ^ d * aeval x Q := by
  classical
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := hQ.degree_eq_sum_deg_support hs
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← hd]
  ring

open MvPolynomial in

theorem aeval_eq_pow_mul_aeval_dehomogenise {K L : Type} [CommRing K] [Field L] [Algebra K L]
    {m : ℕ} {Q : MvPolynomial (Fin (m + 1)) K} {d : ℕ} (hQ : Q.IsHomogeneous d)
    (x : Fin (m + 1) → L) (hx : x 0 ≠ 0) :
    aeval x Q = x 0 ^ d * aeval (fun a : Fin m => x a.succ / x 0)
      (aeval (Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K) Q) := by
  set y : Fin m → L := fun a => x a.succ / x 0 with hy
  have hx' : x = fun a => x 0 * (Fin.cons 1 y : Fin (m + 1) → L) a := by
    funext a
    refine Fin.cases ?_ (fun j => ?_) a
    · simp
    · simp only [Fin.cons_succ, hy]
      field_simp
  have key : (fun i => aeval y ((Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K) i)) =
      (Fin.cons 1 y : Fin (m + 1) → L) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  conv_lhs => rw [hx']
  rw [aeval_mul_of_isHomogeneous_cone hQ,
    aeval_eq_bind₁ (Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K), aeval_bind₁, key]

open MvPolynomial in

theorem dehomogenise_ne_zero_of_isHomogeneous {K : Type} [Field K]
    {m : ℕ} {Q : MvPolynomial (Fin (m + 1)) K} {d : ℕ} (hQ : Q.IsHomogeneous d) (h0 : Q ≠ 0) :
    aeval (Fin.cons 1 X : Fin (m + 1) → MvPolynomial (Fin m) K) Q ≠ 0 := by
  intro h
  have hinj := IsFractionRing.injective (MvPolynomial (Fin (m + 1)) K)
    (FractionRing (MvPolynomial (Fin (m + 1)) K))
  have hx0 : (algebraMap (MvPolynomial (Fin (m + 1)) K) (FractionRing (MvPolynomial (Fin (m + 1)) K)) ∘
      X) 0 ≠ 0 := by
    simp only [Function.comp_apply]
    exact (map_ne_zero_iff _ hinj).mpr (X_ne_zero 0)
  have e := aeval_eq_pow_mul_aeval_dehomogenise (L := FractionRing (MvPolynomial (Fin (m + 1)) K)) hQ
    (algebraMap (MvPolynomial (Fin (m + 1)) K) (FractionRing (MvPolynomial (Fin (m + 1)) K)) ∘ X) hx0
  rw [h, map_zero, mul_zero, aeval_algebraMap_apply, aeval_X_left_apply] at e
  exact h0 (hinj (by rw [e, map_zero]))

theorem exists_coordinates_no_homogeneous_relation_of_generic_zero :
    ∀ (K : Type) [Field K] (σ : K →+* ℂ) (m N : ℕ) (t : Fin m × Fin N → ℂ) (ζ : Fin N → ℂ),
    (∀ Q : MvPolynomial (Fin m × Fin N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → ζ ≠ 0 →
    (∀ i, ∑ j, t (i, j) * ζ j = 0) → ∃ jj : Fin (m + 1) → Fin N,
      ∀ (Q : MvPolynomial (Fin (m + 1)) K) (d : ℕ), Q ≠ 0 → Q.IsHomogeneous d →
        MvPolynomial.eval₂ σ (fun a => ζ (jj a)) Q ≠ 0 := by
  intro K _ σ m N t ζ ht hζ hrel
  let _ : Algebra K ℂ := σ.toAlgebra
  obtain _ | N := N
  · exact absurd (funext fun j => j.elim0) hζ
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hζ
  have hj0' : ζ j0 ≠ 0 := hj0
  have hind : AlgebraicIndependent K t := by
    rw [algebraicIndependent_iff]
    intro p hp
    by_contra hne
    exact ht p hne hp
  obtain ⟨J, hJ⟩ := exists_algebraicIndependent_ratios_of_generic_zero K ℂ m N t ζ j0 hind hj0' hrel
  refine ⟨Fin.cons j0 J, fun Q d hQ0 hQ => ?_⟩
  have e := aeval_eq_pow_mul_aeval_dehomogenise (L := ℂ) hQ
    (fun a => ζ ((Fin.cons j0 J : Fin (m + 1) → Fin (N + 1)) a)) (by simpa using hj0')
  change MvPolynomial.aeval _ Q ≠ 0
  rw [e]
  simp only [Fin.cons_zero, Fin.cons_succ]
  refine mul_ne_zero (pow_ne_zero _ hj0') ?_
  intro h
  exact dehomogenise_ne_zero_of_isHomogeneous hQ hQ0 ((algebraicIndependent_iff.mp hJ) _ h)

end GlobalTheory
