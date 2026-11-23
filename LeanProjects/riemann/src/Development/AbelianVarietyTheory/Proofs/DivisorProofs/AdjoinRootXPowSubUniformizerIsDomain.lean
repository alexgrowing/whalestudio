import Mathlib
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

open Polynomial in

theorem adjoinRoot_X_pow_sub_C_uniformizer_isDomain :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (e : ℕ),
      Irreducible π → 0 < e → IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) := by
  intro R _ _ _ π e hπ he
  have hπp : Prime π := hπ.prime
  have hP : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπp.ne_zero).2 hπp
  have hmon : (X ^ e - C π : R[X]).Monic := monic_X_pow_sub_C _ he.ne'
  have hdeg : (X ^ e - C π : R[X]).natDegree = e := natDegree_X_pow_sub_C
  have hirr : Irreducible (X ^ e - C π : R[X]) := by
    refine Polynomial.IsEisensteinAt.irreducible ⟨?_, ?_, ?_⟩ hP hmon.isPrimitive (by rw [hdeg]; exact he)
    · rw [hmon.leadingCoeff]
      exact fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro n hn
      rw [hdeg] at hn
      rw [coeff_sub, coeff_X_pow, if_neg hn.ne, zero_sub, coeff_C]
      split_ifs
      · exact neg_mem (Ideal.mem_span_singleton_self _)
      · rw [neg_zero]; exact zero_mem _
    · rw [coeff_sub, coeff_X_pow, if_neg he.ne, zero_sub, coeff_C_zero, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      have h1 : π * (1 + π * c) = 0 := by linear_combination -hc
      have h2 := (mul_eq_zero.1 h1).resolve_left hπp.ne_zero
      exact hπ.not_isUnit (IsUnit.of_mul_eq_one (-c) (by linear_combination -h2))
  exact AdjoinRoot.isDomain_of_prime hirr.prime

end GlobalTheory
