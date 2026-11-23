import Mathlib
open NumberField

namespace GlobalTheory.SplitEmbSep

open NumberField in

theorem _root_.GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral {C : Type*} [NormedField C] [IsUltrametricDist C]
    {x : C} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := hx
  by_contra h
  push_neg at h
  rw [← Polynomial.aeval_def, hm.as_sum] at hp
  simp only [map_add, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C,
    algebraMap_int_eq, eq_intCast, map_intCast] at hp
  set n := p.natDegree
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn] at hp
    simp at hp
  have hs : (Finset.range n).Nonempty := Finset.nonempty_range_iff.mpr hn.ne'
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty hs
    (fun i => ((p.coeff i : ℤ) : C) * x ^ i)
  have hxn : x ^ n = -∑ i ∈ Finset.range n, ((p.coeff i : ℤ) : C) * x ^ i :=
    eq_neg_of_add_eq_zero_left hp
  have h1 : ‖x‖ ^ n ≤ ‖x‖ ^ i := by
    calc ‖x‖ ^ n = ‖x ^ n‖ := (norm_pow x n).symm
      _ = ‖∑ i ∈ Finset.range n, ((p.coeff i : ℤ) : C) * x ^ i‖ := by rw [hxn, norm_neg]
      _ ≤ ‖((p.coeff i : ℤ) : C) * x ^ i‖ := hle
      _ = ‖((p.coeff i : ℤ) : C)‖ * ‖x‖ ^ i := by rw [norm_mul, norm_pow]
      _ ≤ 1 * ‖x‖ ^ i := by
        gcongr
        exact IsUltrametricDist.norm_intCast_le_one C _
      _ = ‖x‖ ^ i := one_mul _
  have h2 : ‖x‖ ^ i < ‖x‖ ^ n := pow_lt_pow_right₀ h (Finset.mem_range.mp hi)
  exact absurd h1 (not_le.mpr h2)

open NumberField in

theorem _root_.GlobalTheory.SplitEmbSep.norm_det_lt_one {C ι : Type*} [NormedField C] [IsUltrametricDist C]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι C) (hM : ∀ i j, ‖M i j‖ ≤ 1) (k : ι)
    (hk : ∀ i, ‖M i k‖ < 1) : ‖M.det‖ < 1 := by
  rw [Matrix.det_apply]
  obtain ⟨σ, -, hle⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty
    (Finset.univ_nonempty (α := Equiv.Perm ι))
    (fun σ => Equiv.Perm.sign σ • ∏ i, M (σ i) i)
  refine lt_of_le_of_lt hle ?_
  have hprod : ‖∏ i, M (σ i) i‖ < 1 := by
    rw [norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hk _)
      (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hM _ _))
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simpa [hs, Units.smul_def] using hprod

open NumberField in

theorem _root_.GlobalTheory.SplitEmbSep.one_le_norm_intCast {C : Type*} [NormedField C] [IsUltrametricDist C] {g : ℕ}
    (hg : g.Prime) (hgC : ‖(g : C)‖ < 1) {d : ℤ} (hd : ¬ (g : ℤ) ∣ d) : 1 ≤ ‖(d : C)‖ := by
  obtain ⟨a, b, hab⟩ :=
    ((Nat.prime_iff_prime_int.mp hg).irreducible.coprime_iff_not_dvd).mpr hd
  have hC : (a : C) * (g : C) + (b : C) * (d : C) = 1 := by exact_mod_cast congrArg (Int.cast (R := C)) hab
  have h1 : ‖(a : C) * (g : C)‖ < 1 := by
    rw [norm_mul]
    calc ‖(a : C)‖ * ‖(g : C)‖ ≤ 1 * ‖(g : C)‖ := by
          gcongr
          exact IsUltrametricDist.norm_intCast_le_one C a
      _ < 1 := by rwa [one_mul]
  have h2 : 1 ≤ max ‖(a : C) * (g : C)‖ ‖(b : C) * (d : C)‖ := by
    rw [← norm_one (α := C), ← hC]
    exact IsUltrametricDist.norm_add_le_max _ _
  have h3 : 1 ≤ ‖(b : C) * (d : C)‖ := by
    rcases le_max_iff.mp h2 with h | h
    · exact absurd h (not_le.mpr h1)
    · exact h
  calc 1 ≤ ‖(b : C)‖ * ‖(d : C)‖ := by rwa [← norm_mul]
    _ ≤ 1 * ‖(d : C)‖ := by
      gcongr
      exact IsUltrametricDist.norm_intCast_le_one C b
    _ = ‖(d : C)‖ := one_mul _

open NumberField in

theorem _root_.GlobalTheory.SplitEmbSep.not_dvd_discr_of_split {g : ℕ} (hg : g.Prime) (E : Type*) [Field E]
    [NumberField E]
    (h : (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E) :
    ¬ (g : ℤ) ∣ discr E := by
  have hgp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  set p : Ideal ℤ := Ideal.span {(g : ℤ)} with hp_def
  have hp0 : p ≠ ⊥ := by simpa [hp_def] using hgp.ne_zero
  haveI hpprime : p.IsPrime := (Ideal.span_singleton_prime hgp.ne_zero).mpr hgp
  haveI hpmax : p.IsMaximal := hpprime.isMaximal hp0
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) ℚ E hp0
  have hcard : (IsDedekindDomain.primesOverFinset p (𝓞 E)).card = Module.finrank ℚ E := by
    rw [← h, ← IsDedekindDomain.coe_primesOverFinset hp0, Set.ncard_coe_finset]
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) p ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))]
    exact hp0
  have hge : ∀ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 E),
      1 ≤ p.ramificationIdx' P * p.inertiaDeg' P := by
    intro P hP
    have hP' : P ∈ p.primesOver (𝓞 E) := by
      rw [← IsDedekindDomain.coe_primesOverFinset hp0]
      exact hP
    haveI := hP'.1
    haveI := hP'.2
    have he : p.ramificationIdx' P ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero hmap hP'.1
        (Ideal.map_le_iff_le_comap.mpr (le_of_eq (Ideal.over_def P p)))
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero he (Ideal.inertiaDeg'_pos p P).ne')
  have hone := (Finset.sum_eq_sum_iff_of_le hge).mp (by
    rw [← Finset.card_eq_sum_ones, hcard, hsum])
  rw [NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hgp]
  intro P hPprime hgP
  have hunder : p = P.under ℤ := by
    have hle : p ≤ P.under ℤ := by
      rw [hp_def, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_comap.mpr (by simpa using hgP)
    exact hpmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
  haveI : P.LiesOver p := ⟨hunder⟩
  have hPF : P ∈ IsDedekindDomain.primesOverFinset p (𝓞 E) := by
    rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hp0]
    exact ⟨hPprime, this⟩
  have he := Nat.eq_one_of_mul_eq_one_right (hone P hPF).symm
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
    ← Ideal.ramificationIdx'_eq_ramificationIdx p P hp0]
  exact he

end GlobalTheory.SplitEmbSep
