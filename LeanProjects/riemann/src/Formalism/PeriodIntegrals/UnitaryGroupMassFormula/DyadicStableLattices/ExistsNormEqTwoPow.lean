import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.AlgebraMapMkO

noncomputable section

namespace PI.GoodTwo.AlgebraicValuationTrichotomy

open NumberField QuadraticAlgebra
open scoped nonZeroDivisors

theorem core (m : ℕ) [Fact (∀ r : ℚ, r ^ 2 ≠ -(m : ℚ) + 1 * r)] (d : ℕ) (hd : Squarefree d)
    (hdm : d + 1 = 4 * m) (hme : Even m) :
    ∃ (h : ℕ) (x y : ℤ), 0 < h ∧ Odd y ∧ x ^ 2 + x * y + (m : ℤ) * y ^ 2 = 2 ^ h := by
  classical
  obtain ⟨k, hk⟩ := hme
  have hk' : (m : ℤ) = 2 * k := by push_cast [hk]; ring
  have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  set w : 𝓞 (Kq m) := mkO m 0 1 with hw
  set v : 𝓞 (Kq m) := mkO m 1 (-1) with hv
  set P : Ideal (𝓞 (Kq m)) := Ideal.span {2, w} with hP
  set Q : Ideal (𝓞 (Kq m)) := Ideal.span {2, v} with hQ
  have hwP : w ∈ P := by rw [hP]; exact Ideal.subset_span (by simp)
  have h2P : (2 : 𝓞 (Kq m)) ∈ P := by rw [hP]; exact Ideal.subset_span (by simp)
  have hvQ : v ∈ Q := by rw [hQ]; exact Ideal.subset_span (by simp)
  have h2Q : (2 : 𝓞 (Kq m)) ∈ Q := by rw [hQ]; exact Ideal.subset_span (by simp)
  have hwv : w + v = 1 := by
    rw [hw, hv, mkO_add, one_O m]; norm_num
  have hPQ : P ⊔ Q = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hwv]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hwP) (Ideal.mem_sup_right hvQ)
  have hwv' : w * v = mkO m m 0 := by
    rw [hw, hv, mkO_mul]; congr 1 <;> ring
  have hm2 : mkO m m 0 = 2 * mkO m k 0 := by
    rw [two_O m, mkO_mul]
    congr 1 <;> (try rw [hk']) <;> ring
  have hPQ2 : P * Q = Ideal.span {2} := by
    apply le_antisymm
    · rw [hP, hQ, Ideal.span_mul_span', Ideal.span_le]
      rintro _ ⟨a, ha, b, hb, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rw [SetLike.mem_coe, Ideal.mem_span_singleton]
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact dvd_mul_right _ _
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
      · show (2 : 𝓞 (Kq m)) ∣ w * v
        rw [hwv', hm2]; exact dvd_mul_right _ _
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have h2 : (2 : 𝓞 (Kq m)) = 2 * v + w * 2 := by linear_combination (-2) * hwv
      rw [h2]
      exact Ideal.add_mem _ (Ideal.mul_mem_mul h2P hvQ) (Ideal.mul_mem_mul hwP h2Q)
  have h2ne : (2 : 𝓞 (Kq m)) ≠ 0 := two_ne_zero
  have hP0 : P ∈ (Ideal (𝓞 (Kq m)))⁰ := by
    refine mem_nonZeroDivisors_of_ne_zero fun h => h2ne ?_
    have := h2P
    rwa [h, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  obtain ⟨n, hnpos, hprin⟩ : ∃ n, 0 < n ∧ (P ^ n).IsPrincipal := by
    refine ⟨orderOf (ClassGroup.mk0 (⟨P, hP0⟩ : (Ideal (𝓞 (Kq m)))⁰)),
      orderOf_pos _, ?_⟩
    have hpow : ClassGroup.mk0 ((⟨P, hP0⟩ : (Ideal (𝓞 (Kq m)))⁰) ^
        orderOf (ClassGroup.mk0 (⟨P, hP0⟩ : (Ideal (𝓞 (Kq m)))⁰))) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    rw [ClassGroup.mk0_eq_one_iff] at hpow
    exact hpow
  obtain ⟨α, hαspan⟩ : ∃ α, Ideal.span {α} = P ^ n :=
    ⟨_, Ideal.span_singleton_generator (P ^ n)⟩
  have hQmap : Ideal.map (RingOfIntegers.mapRingHom (starRingEnd (Kq m))) P = Q := by
    rw [hP, hQ, Ideal.map_span, Set.image_pair, map_ofNat, hw, star_O]
    norm_num [hv]
  have hQn : Ideal.span {RingOfIntegers.mapRingHom (starRingEnd (Kq m)) α} =
      Q ^ n := by
    rw [← hQmap, ← Ideal.map_pow, ← hαspan, Ideal.map_span, Set.image_singleton]
  have hprod : Ideal.span {α * RingOfIntegers.mapRingHom (starRingEnd (Kq m)) α} =
      Ideal.span {(2 : 𝓞 (Kq m)) ^ n} := by
    rw [← Ideal.span_singleton_mul_span_singleton, hαspan, hQn, ← mul_pow, hPQ2,
      Ideal.span_singleton_pow]
  rw [Ideal.span_singleton_eq_span_singleton] at hprod
  obtain ⟨x, y, hxy⟩ := repr_O m d hd hdm α
  have hN : α * RingOfIntegers.mapRingHom (starRingEnd (Kq m)) α =
      mkO m (x ^ 2 + x * y + (m : ℤ) * y ^ 2) 0 := by
    rw [hxy, star_O, mkO_mul]; congr 1 <;> ring
  rw [hN, pow_two_O m] at hprod
  have hN0 : 0 ≤ x ^ 2 + x * y + (m : ℤ) * y ^ 2 := by
    nlinarith [sq_nonneg (2 * x + y), sq_nonneg y, mul_nonneg (sub_nonneg.2 hm1) (sq_nonneg y)]
  have hNeq : x ^ 2 + x * y + (m : ℤ) * y ^ 2 = 2 ^ n :=
    Int.dvd_antisymm hN0 (pow_nonneg (by norm_num) _)
      (int_dvd m d hd hdm hprod.dvd)
      (int_dvd m d hd hdm hprod.symm.dvd)
  refine ⟨n, x, y, hnpos, ?_, hNeq⟩
  by_contra hyo
  rw [Int.not_odd_iff_even] at hyo
  obtain ⟨l, hl⟩ := hyo
  have hx : Even x := by
    by_contra hxo
    rw [Int.not_even_iff_odd] at hxo
    obtain ⟨j, hj⟩ := hxo
    have h2n : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h1 : (1 : ℤ) = 2 * (2 ^ (n - 1) - 2 * j ^ 2 - 2 * j - 2 * j * l - l - 2 * m * l ^ 2) := by
      subst hj hl; linear_combination hNeq + h2n
    exact absurd (Dvd.intro _ h1.symm) (by norm_num)
  obtain ⟨j, hj⟩ := hx
  have hα2 : α = 2 * mkO m j l := by
    rw [hxy, hj, hl, two_O m, mkO_mul]; congr 1 <;> ring
  have hPnQ : P ^ n ≤ Q := by
    rw [← hαspan, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hα2]
    exact Ideal.mul_mem_right _ _ h2Q
  have hQtop : Q = ⊤ := by
    have := Ideal.pow_sup_eq_top (n := n) hPQ
    rwa [sup_eq_right.mpr hPnQ] at this
  have hw2 : w ∈ Ideal.span {(2 : 𝓞 (Kq m))} := by
    rw [← hPQ2, hQtop, Ideal.mul_top]; exact hwP
  rw [Ideal.mem_span_singleton] at hw2
  obtain ⟨γ, hγ⟩ := hw2
  obtain ⟨a, b, rfl⟩ := repr_O m d hd hdm γ
  rw [hw, two_O m, mkO_mul] at hγ
  have := (mkO_inj m hγ).2
  omega

theorem exists_norm_eq_two_pow (d : ℕ) (hd : Squarefree d) (h7 : d % 8 = 7) :
    ∃ (h : ℕ) (x y : ℤ), 0 < h ∧ Odd y ∧
      x ^ 2 + x * y + (((d + 1) / 4 : ℕ) : ℤ) * y ^ 2 = 2 ^ h := by
  have hm : 1 ≤ (d + 1) / 4 := by omega
  have : Fact (∀ r : ℚ, r ^ 2 ≠ -(((d + 1) / 4 : ℕ) : ℚ) + 1 * r) :=
    ⟨noRoot _ hm⟩
  exact core ((d + 1) / 4) d hd (by omega) ⟨(d + 1) / 8, by omega⟩

end PI.GoodTwo.AlgebraicValuationTrichotomy
