import Mathlib

namespace ReciprocityTheory.MultiplicativeHeights

namespace DerivationAlgebraicIndependence

open MvPolynomial

theorem derivation_aeval_eq {K R ι : Type*} [CommRing K] [CommRing R] [Algebra K R] [Fintype ι]
    (d : Derivation K R R) (z : ι → R) (P : MvPolynomial ι K) :
    d (aeval z P) = ∑ i, aeval z (pderiv i P) * d (z i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hp, smul_eq_mul, pderiv_X, Pi.single_apply,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [map_add, map_mul, aeval_X, apply_ite (aeval z), map_zero, map_one, add_mul, mul_ite,
      mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    ring

theorem totalDegree_pderiv_lt {K ι : Type*} [CommRing K] (P : MvPolynomial ι K) (i : ι)
    (hP : 0 < P.totalDegree) : (pderiv i P).totalDegree < P.totalDegree := by
  classical
  have hsum : pderiv i P = ∑ m ∈ P.support, pderiv i (monomial m (coeff m P)) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
  rw [hsum]
  refine lt_of_le_of_lt (totalDegree_finset_sum _ _) ?_
  rw [Finset.sup_lt_iff hP]
  intro m hm
  rw [pderiv_monomial]
  by_cases hmi : m i = 0
  · simp [hmi, hP]
  · have hm1 : m = (m - Finsupp.single i 1) + Finsupp.single i 1 := by
      ext k
      by_cases hk : k = i
      · subst hk; simp; omega
      · simp [Finsupp.single_apply, Ne.symm hk]
    have key : ((m - Finsupp.single i 1).sum fun _ e => e) + 1 = m.sum fun _ e => e := by
      conv_rhs => rw [hm1]
      rw [Finsupp.sum_add_index' (by simp) (by intros; rfl), Finsupp.sum_single_index rfl]
    have hle : (m.sum fun _ e => e) ≤ P.totalDegree := le_totalDegree hm
    refine lt_of_le_of_lt (totalDegree_monomial_le _ _) ?_
    show ((m - Finsupp.single i 1).sum fun _ e => e) < _
    omega

theorem eq_C_of_pderiv_eq_zero {K ι : Type*} [Field K] [CharZero K] (P : MvPolynomial ι K)
    (h : ∀ i, pderiv i P = 0) : P.totalDegree = 0 := by
  classical
  by_contra hne
  obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup P.support
    (Finset.nonempty_of_ne_empty (by rintro hs; apply hne; simp [totalDegree, hs]))
    (fun s => s.sum fun _ e => e)
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hne
    simpa [totalDegree] using hmd
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hm0 (Finsupp.ext hc)
  have hc := congrArg (coeff (m - Finsupp.single i 1)) (h i)
  rw [coeff_pderiv, coeff_zero] at hc
  have hm' : m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
    ext k
    by_cases hk : k = i
    · subst hk; simp; omega
    · simp [Finsupp.single_apply, Ne.symm hk]
  rw [hm'] at hc
  rcases mul_eq_zero.mp hc with h1 | h1
  · exact (mem_support_iff.mp hm) h1
  · exact Nat.cast_add_one_ne_zero _ h1

theorem algebraicIndependent_of_derivations {K R ι J : Type*} [Field K] [CharZero K] [CommRing R]
    [Nontrivial R] [Algebra K R] [Fintype ι] (z : ι → R) (δ : J → Derivation K R R)
    (h : ∀ c : ι → R, (∀ j, ∑ i, c i * δ j (z i) = 0) → ∀ i, c i = 0) :
    AlgebraicIndependent K z := by
  classical
  rw [algebraicIndependent_iff]
  suffices H : ∀ n (P : MvPolynomial ι K), P.totalDegree = n → aeval z P = 0 → P = 0 from
    fun P => H _ P rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hP
  have hd : ∀ i, pderiv i P = 0 := by
    have hv : ∀ i, aeval z (pderiv i P) = 0 :=
      h (fun i => aeval z (pderiv i P)) (fun j => by rw [← derivation_aeval_eq, hP, map_zero])
    intro i
    by_cases h0 : P.totalDegree = 0
    · rw [totalDegree_eq_zero_iff_eq_C] at h0
      rw [h0]
      simp
    · exact ih _ (hn ▸ totalDegree_pderiv_lt P i (Nat.pos_of_ne_zero h0)) _ rfl (hv i)
  have h0 := eq_C_of_pderiv_eq_zero P hd
  rw [totalDegree_eq_zero_iff_eq_C] at h0
  rw [h0, aeval_C] at hP
  have hc : coeff 0 P = 0 := (algebraMap K R).injective (hP.trans (map_zero _).symm)
  rw [h0, hc, map_zero]

end DerivationAlgebraicIndependence

end ReciprocityTheory.MultiplicativeHeights
