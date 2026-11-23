import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom

namespace ReciprocityTheory.AnForm.R

open IsLocalRing

variable {R : Type*} [CommRing R]

theorem exists_le_associated_of_dvd_prod_primes [IsDomain R] {ι : Type*} (f : ι → R) :
    ∀ (s : Multiset ι), (∀ i ∈ s, Prime (f i)) → ∀ {x : R}, x ∣ (s.map f).prod →
      ∃ t ≤ s, Associated x (t.map f).prod := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    intro _ x hx
    refine ⟨0, le_refl _, ?_⟩
    simp only [Multiset.map_zero, Multiset.prod_zero] at hx ⊢
    exact associated_one_iff_isUnit.2 (isUnit_of_dvd_one hx)
  | cons a s ih =>
    intro hs x hx
    have ha : Prime (f a) := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ i ∈ s, Prime (f i) := fun i hi => hs i (Multiset.mem_cons_of_mem hi)
    rw [Multiset.map_cons, Multiset.prod_cons] at hx
    by_cases hax : f a ∣ x
    · obtain ⟨y, rfl⟩ := hax
      have hy : y ∣ (s.map f).prod := (mul_dvd_mul_iff_left ha.ne_zero).1 hx
      obtain ⟨t, ht, hyt⟩ := ih hs' hy
      refine ⟨a ::ₘ t, Multiset.cons_le_cons a ht, ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact hyt.mul_left (f a)
    · obtain ⟨z, hz⟩ := hx
      have h1 : f a ∣ x * z := ⟨(s.map f).prod, hz.symm⟩
      have h2 : f a ∣ z := (ha.dvd_or_dvd h1).resolve_left hax
      obtain ⟨w, rfl⟩ := h2
      have h3 : (s.map f).prod = x * w := by
        apply mul_left_cancel₀ ha.ne_zero
        rw [hz]
        ring
      obtain ⟨t, ht, hxt⟩ := ih hs' ⟨w, h3⟩
      exact ⟨t, ht.trans (Multiset.le_cons_self s a), hxt⟩

theorem prime_of_regular_params [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (i : Fin n) : Prime (f i) := by
  have hm : f i ∈ maximalIdeal R := by
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  exact prime_of_not_mem_sq hm ((regular_params_spec f hspan hdim).1 i)

theorem eq_unit_mul_monomial [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (J : Finset (Fin n)) {x : R} (hx0 : x ≠ 0) (hrad : (∏ i ∈ J, f i) ∈ (Ideal.span {x}).radical) :
    ∃ (u : Rˣ) (m : Fin n → ℕ), (∀ i, i ∉ J → m i = 0) ∧ x = u * ∏ i ∈ J, f i ^ m i := by
  obtain ⟨k, hk⟩ := hrad
  rw [Ideal.mem_span_singleton] at hk
  have hprimes : ∀ i ∈ k • J.val, Prime (f i) := fun i _ => prime_of_regular_params f hspan hdim i
  have hprod : ((k • J.val).map f).prod = (∏ i ∈ J, f i) ^ k := by
    rw [Multiset.map_nsmul, Multiset.prod_nsmul]
    rfl
  rw [← hprod] at hk
  obtain ⟨t, ht, hxt⟩ := exists_le_associated_of_dvd_prod_primes f (k • J.val) hprimes hk
  have htJ : ∀ i, i ∉ J → Multiset.count i t = 0 := fun i hi => Multiset.count_eq_zero.2 fun hit =>
    hi (Multiset.mem_of_mem_nsmul (Multiset.mem_of_le ht hit))
  obtain ⟨u, hu⟩ := hxt.symm
  refine ⟨u, fun i => Multiset.count i t, htJ, ?_⟩
  rw [← hu, Finset.prod_multiset_map_count, mul_comm]
  congr 1
  apply Finset.prod_subset
  · intro i hi
    by_contra hiJ
    exact Multiset.count_ne_zero.2 (Multiset.mem_toFinset.1 hi) (htJ i hiJ)
  · intro i _ hi
    rw [Multiset.count_eq_zero.2 (fun h => hi (Multiset.mem_toFinset.2 h)), pow_zero]

theorem ord_localization_eq_exponent [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (J : Finset (Fin n)) (u : Rˣ) (m : Fin n → ℕ) (i : Fin n) (hi : i ∈ J)
    [(Ideal.span {f i}).IsPrime] :
    Ring.ord (Localization.AtPrime (Ideal.span {f i}))
        (algebraMap R (Localization.AtPrime (Ideal.span {f i})) (u * ∏ j ∈ J, f j ^ m j)) =
      (m i : ℕ∞) := by
  have : IsDomain R := isDomain_of_isRegularLocalRing
  set P := Ideal.span {f i} with hP
  set S := Localization.AtPrime P
  have hpr : ∀ j, Prime (f j) := prime_of_regular_params f hspan hdim

  have hout : ∀ j, j ≠ i → f j ∉ P := by
    intro j hji hj
    rw [hP, Ideal.mem_span_singleton] at hj
    obtain ⟨c, hc⟩ := hj
    have hdc : f j ∣ f i * c := ⟨1, by rw [mul_one, hc]⟩
    rcases (hpr j).dvd_or_dvd hdc with h | h
    · exact (regular_params_spec f hspan hdim).2 j i hji
        (associated_of_dvd_dvd h ⟨c, hc⟩)
    · obtain ⟨d, rfl⟩ := h
      have : f j * 1 = f j * (f i * d) := by linear_combination hc
      have h1 := mul_left_cancel₀ (hpr j).ne_zero this
      exact (hpr i).not_isUnit (isUnit_of_dvd_one ⟨d, h1⟩)
  have hunit : ∀ j, j ≠ i → IsUnit (algebraMap R S (f j)) := fun j hj =>
    IsLocalization.map_units S (⟨f j, hout j hj⟩ : P.primeCompl)
  set π := algebraMap R S (f i)
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors P)
  have hπ0 : π ≠ 0 := fun h => (hpr i).ne_zero (hinj (by rw [map_zero]; exact h))
  have hπnzd : π ∈ nonZeroDivisors S := mem_nonZeroDivisors_of_ne_zero hπ0
  have hmax : Ideal.span {π} = maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    show Ideal.span {π} = Ideal.map (algebraMap R S) (Ideal.span {f i})
    rw [Ideal.map_span, Set.image_singleton]
  have hord1 : Ring.ord S π = 1 := by
    unfold Ring.ord
    rw [hmax, Module.length_eq_one_iff]
    exact isSimpleModule_iff_isCoatom.mpr
      (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal S))
  rw [← Finset.mul_prod_erase J _ hi, map_mul, map_mul, map_pow,
    Ring.ord_mul_of_isUnit_left ((Units.isUnit u).map _)]
  have hrest : IsUnit (algebraMap R S (∏ j ∈ J.erase i, f j ^ m j)) := by
    rw [map_prod]
    exact IsUnit.prod_iff.mpr fun j hj => by
      rw [map_pow]; exact (hunit j (Finset.ne_of_mem_erase hj)).pow _
  rw [Ring.ord_mul_of_isUnit_right hrest, Ring.ord_pow hπnzd, hord1, nsmul_eq_mul, mul_one]

end ReciprocityTheory.AnForm.R
