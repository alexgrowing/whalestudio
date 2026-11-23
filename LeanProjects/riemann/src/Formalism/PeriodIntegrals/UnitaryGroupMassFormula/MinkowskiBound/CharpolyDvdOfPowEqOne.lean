import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.PowerSumStep

namespace PI.Mk

open Polynomial Matrix

theorem charpoly_dvd_of_pow_eq_one {R : Type*} [CommRing R] {N : ℕ} (A : Matrix (Fin N) (Fin N) R)
    (n : ℕ) (h : A ^ n = 1) : A.charpoly ∣ (X ^ n - 1 : R[X]) ^ N := by
  have hcomm : Commute (scalar (Fin N) (X : R[X])) ((C : R →+* R[X]).mapMatrix A) :=
    scalar_commute (r := (X : R[X])) (fun r' => Commute.all _ r') _
  have hMn : ((C : R →+* R[X]).mapMatrix A) ^ n = 1 := by rw [← map_pow, h, map_one]
  have key : (∑ i ∈ Finset.range n, scalar (Fin N) (X : R[X]) ^ i *
      ((C : R →+* R[X]).mapMatrix A) ^ (n - 1 - i)) *
      (scalar (Fin N) (X : R[X]) - (C : R →+* R[X]).mapMatrix A)
      = scalar (Fin N) ((X : R[X]) ^ n - 1) := by
    rw [hcomm.geom_sum₂_mul, hMn, map_sub, map_pow, map_one]
  have hs : ∀ c : R[X], (scalar (Fin N) c).det = c ^ N := by
    intro c
    rw [scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine Dvd.intro_left (∑ i ∈ Finset.range n, scalar (Fin N) (X : R[X]) ^ i *
      ((C : R →+* R[X]).mapMatrix A) ^ (n - 1 - i)).det ?_
  rw [← hs ((X : R[X]) ^ n - 1), ← key, det_mul]
  rfl

def Good (ℓ : ℕ) (p : ℚ[X]) : Prop :=
  p.Monic ∧ ∃ y : ℕ, (ℓ - 1) * y ≤ p.natDegree ∧
    -p.nextCoeff = (p.natDegree : ℚ) - (ℓ : ℚ) * (y : ℚ) ∧ (y = 0 → p = (X - 1) ^ p.natDegree)

theorem good_one (ℓ : ℕ) : Good ℓ 1 :=
  ⟨monic_one, 0, by simp, by simp [nextCoeff], fun _ => by simp⟩

theorem good_mul (ℓ : ℕ) (p q : ℚ[X]) (hp : Good ℓ p) (hq : Good ℓ q) : Good ℓ (p * q) := by
  obtain ⟨hpm, y, hy1, hy2, hy3⟩ := hp
  obtain ⟨hqm, z, hz1, hz2, hz3⟩ := hq
  have hdeg : (p * q).natDegree = p.natDegree + q.natDegree := hpm.natDegree_mul hqm
  refine ⟨hpm.mul hqm, y + z, ?_, ?_, ?_⟩
  · rw [hdeg, mul_add]; exact add_le_add hy1 hz1
  · rw [hpm.nextCoeff_mul hqm, hdeg]; push_cast; linear_combination hy2 + hz2
  · intro h0
    have hy : y = 0 := by omega
    have hz : z = 0 := by omega
    rw [hdeg, pow_add]
    conv_lhs => rw [hy3 hy, hz3 hz]

theorem nextCoeff_X_pow_sub_one (n : ℕ) (hn : 0 < n) :
    (X ^ n - 1 : ℚ[X]).nextCoeff = if n = 1 then -1 else 0 := by
  have hdeg : (X ^ n - 1 : ℚ[X]).natDegree = n := by
    simpa using natDegree_X_pow_sub_C (R := ℚ) (n := n) (r := 1)
  rw [nextCoeff_of_natDegree_pos (by rw [hdeg]; exact hn), hdeg]
  split_ifs with h1
  · subst h1; simp
  · have h2 : n - 1 ≠ n := by omega
    have h3 : n - 1 ≠ 0 := by omega
    simp [coeff_X_pow, coeff_one, h2, h3]

theorem good_cyclotomic_one (ℓ : ℕ) : Good ℓ (cyclotomic 1 ℚ) := by
  rw [cyclotomic_one, ← C_1]
  refine ⟨monic_X_sub_C 1, 0, by simp, ?_, fun _ => ?_⟩
  · rw [natDegree_X_sub_C, nextCoeff_X_sub_C]; simp
  · rw [natDegree_X_sub_C, pow_one, C_1]

theorem good_cyclotomic_succ (ℓ : ℕ) (hℓ : ℓ.Prime) (j : ℕ) :
    Good ℓ (cyclotomic (ℓ ^ (j + 1)) ℚ) := by
  have := Fact.mk hℓ
  have h2 : 2 ≤ ℓ := hℓ.two_le
  have hmon : (cyclotomic (ℓ ^ (j + 1)) ℚ).Monic := cyclotomic.monic _ ℚ
  have hdeg : (cyclotomic (ℓ ^ (j + 1)) ℚ).natDegree = ℓ ^ j * (ℓ - 1) := by
    rw [natDegree_cyclotomic, Nat.totient_prime_pow_succ hℓ]
  have hm1 : ((X : ℚ[X]) ^ ℓ ^ j - 1).Monic := by
    simpa using monic_X_pow_sub_C (1 : ℚ) (pow_pos hℓ.pos j).ne'
  have hnc := congrArg nextCoeff
    (cyclotomic_prime_pow_mul_X_pow_sub_one (R := ℚ) (p := ℓ) (k := j))
  rw [hmon.nextCoeff_mul hm1, nextCoeff_X_pow_sub_one _ (pow_pos hℓ.pos j),
    nextCoeff_X_pow_sub_one _ (pow_pos hℓ.pos (j + 1))] at hnc
  have hne : ℓ ^ (j + 1) ≠ 1 := (Nat.one_lt_pow (by omega) hℓ.one_lt).ne'
  rw [if_neg hne] at hnc
  rcases j with _ | k
  · rw [pow_zero, if_pos rfl] at hnc
    refine ⟨hmon, 1, ?_, ?_, fun h => absurd h one_ne_zero⟩
    · rw [hdeg]; simp
    · have hc : (((ℓ ^ 0 * (ℓ - 1) : ℕ)) : ℚ) = (ℓ : ℚ) - 1 := by
        rw [pow_zero, one_mul, Nat.cast_sub (by omega), Nat.cast_one]
      rw [hdeg, hc]; push_cast; linarith
  · have hne' : ℓ ^ (k + 1) ≠ 1 := (Nat.one_lt_pow (by omega) hℓ.one_lt).ne'
    rw [if_neg hne'] at hnc
    have hz : nextCoeff (cyclotomic (ℓ ^ (k + 1 + 1)) ℚ) = 0 := by linarith
    refine ⟨hmon, ℓ ^ k * (ℓ - 1), ?_, ?_, ?_⟩
    · rw [hdeg]
      calc (ℓ - 1) * (ℓ ^ k * (ℓ - 1)) ≤ ℓ * (ℓ ^ k * (ℓ - 1)) :=
            Nat.mul_le_mul_right _ (Nat.sub_le ℓ 1)
        _ = ℓ ^ (k + 1) * (ℓ - 1) := by ring
    · rw [hdeg, hz]; push_cast; ring
    · intro h
      exact absurd h (mul_ne_zero (pow_ne_zero _ hℓ.ne_zero) (by omega))

theorem good_cyclotomic (ℓ : ℕ) (hℓ : ℓ.Prime) (j : ℕ) : Good ℓ (cyclotomic (ℓ ^ j) ℚ) := by
  rcases j with _ | j
  · rw [pow_zero]; exact good_cyclotomic_one ℓ
  · exact good_cyclotomic_succ ℓ hℓ j

theorem good_of_dvd (ℓ : ℕ) (hℓ : ℓ.Prime) (a M : ℕ) (p : ℚ[X]) (hp : p.Monic)
    (hd : p ∣ (X ^ (ℓ ^ a) - 1 : ℚ[X]) ^ M) : Good ℓ p := by
  suffices H : ∀ n : ℕ, ∀ q : ℚ[X], q.natDegree = n → q.Monic →
      q ∣ (X ^ (ℓ ^ a) - 1 : ℚ[X]) ^ M → Good ℓ q from H _ p rfl hp hd
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih q hqn hq hqd
  by_cases h1 : q = 1
  · rw [h1]; exact good_one ℓ
  have hq0 : q ≠ 0 := hq.ne_zero
  have hqu : ¬ IsUnit q := fun hu => h1 (hq.eq_one_of_isUnit hu)
  obtain ⟨r, hr, hrq⟩ := WfDvdMonoid.exists_irreducible_factor hqu hq0
  have hrd : r ∣ (X ^ (ℓ ^ a) - 1 : ℚ[X]) := hr.prime.dvd_of_dvd_pow (hrq.trans hqd)
  rw [← prod_cyclotomic_eq_X_pow_sub_one (pow_pos hℓ.pos a) (R := ℚ)] at hrd
  obtain ⟨d, hdm, hdr⟩ := hr.prime.exists_mem_finset_dvd hrd
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hℓ).1 (Nat.dvd_of_mem_divisors hdm)
  have hirr := cyclotomic.irreducible_rat (pow_pos hℓ.pos i)
  obtain ⟨s, rfl⟩ := (hr.dvd_symm hirr hdr).trans hrq
  have hcm : (cyclotomic (ℓ ^ i) ℚ).Monic := cyclotomic.monic _ ℚ
  have hs : s.Monic := hcm.of_mul_monic_left hq
  have hdeg : (cyclotomic (ℓ ^ i) ℚ * s).natDegree =
      (cyclotomic (ℓ ^ i) ℚ).natDegree + s.natDegree := hcm.natDegree_mul hs
  have hpos : 0 < (cyclotomic (ℓ ^ i) ℚ).natDegree := by
    rw [natDegree_cyclotomic]
    exact Nat.totient_pos.2 (pow_pos hℓ.pos i)
  apply good_mul
  · exact good_cyclotomic ℓ hℓ i
  · exact ih s.natDegree (by omega) s rfl hs ((Dvd.intro_left _ rfl).trans hqd)

theorem eq_one_of_unipotent {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (n : ℕ) (hn : 0 < n)
    (h : A ^ n = 1) (hu : (A - 1) ^ N = 0) : A = 1 := by
  obtain ⟨S, hSdef⟩ : ∃ S : Matrix (Fin N) (Fin N) ℚ, S = ∑ i ∈ Finset.range n, A ^ i :=
    ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Matrix (Fin N) (Fin N) ℚ,
      T = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, A ^ j := ⟨_, rfl⟩
  have hSB : S * (A - 1) = 0 := by rw [hSdef, geom_sum_mul, h, sub_self]
  have hST : S = (n : Matrix (Fin N) (Fin N) ℚ) + T * (A - 1) := by
    rw [hSdef, hTdef, Finset.sum_mul]
    simp_rw [geom_sum_mul]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    abel
  have hcomm : Commute T (A - 1) := by
    rw [hTdef]
    refine Commute.sum_left _ _ _ (fun i _ => Commute.sum_left _ _ _ (fun j _ => ?_))
    exact ((Commute.refl A).sub_right (Commute.one_right A)).pow_left j
  have hnil : IsNilpotent (T * (A - 1)) := ⟨N, by rw [hcomm.mul_pow, hu, mul_zero]⟩
  have hnu : IsUnit (n : Matrix (Fin N) (Fin N) ℚ) := by
    have : IsUnit (n : ℚ) := (Nat.cast_ne_zero.2 hn.ne').isUnit
    simpa using this.map (algebraMap ℚ (Matrix (Fin N) (Fin N) ℚ))
  have hSu : IsUnit S := by
    rw [hST]
    exact hnil.isUnit_add_left_of_commute hnu (Nat.cast_commute n _).symm
  exact sub_eq_zero.1 (hSu.mul_right_eq_zero.1 hSB)

theorem traceStep : TraceStep := by
  intro N ℓ a hℓ g hg
  have h2 : 2 ≤ ℓ := hℓ.two_le
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin N) (Fin N) ℚ, A = (Int.castRingHom ℚ).mapMatrix g :=
    ⟨_, rfl⟩
  have hAn : A ^ (ℓ ^ a) = 1 := by rw [hA, ← map_pow, hg, map_one]
  have hdvd := charpoly_dvd_of_pow_eq_one A _ hAn
  obtain ⟨y, hy1, hy2, hy3⟩ :=
    (good_of_dvd ℓ hℓ a N A.charpoly (charpoly_monic A) hdvd).2
  have hdeg : A.charpoly.natDegree = N := by
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  have htr : A.trace = -A.charpoly.nextCoeff := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp [Matrix.trace, nextCoeff]
    · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
      rw [trace_eq_neg_charpoly_coeff, nextCoeff_of_natDegree_pos (by rw [hdeg]; exact hN),
        hdeg, Fintype.card_fin]
  have htrg : A.trace = ((g.trace : ℤ) : ℚ) := by
    rw [hA]; simp [Matrix.trace, Matrix.diag, RingHom.mapMatrix_apply]
  have hT : ((g.trace : ℤ) : ℚ) = (N : ℚ) - (ℓ : ℚ) * (y : ℚ) := by
    rw [← htrg, htr, hy2, hdeg]
  refine ⟨y, ?_, by exact_mod_cast hT, ?_⟩
  · rw [hdeg] at hy1
    exact (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact hy1)
  · intro hy0
    have hcp := hy3 hy0
    rw [hdeg] at hcp
    have hch := aeval_self_charpoly A
    rw [hcp] at hch
    simp only [map_pow, map_sub, aeval_X, map_one] at hch
    have hA1 := eq_one_of_unipotent A (ℓ ^ a) (pow_pos hℓ.pos a) hAn hch
    ext i j
    have hij := congrFun (congrFun hA1 i) j
    rw [hA, RingHom.mapMatrix_apply, Matrix.map_apply] at hij
    rw [Matrix.one_apply] at hij ⊢
    split_ifs at hij ⊢ <;> simpa using hij

end PI.Mk
