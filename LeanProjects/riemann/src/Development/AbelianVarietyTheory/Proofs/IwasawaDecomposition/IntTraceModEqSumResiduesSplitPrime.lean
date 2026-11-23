import Mathlib

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.SplitTrace

variable {K : Type} [Field K] [NumberField K]

theorem absNorm_span_natCast (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ Module.finrank ℚ K := by
  rw [Ideal.absNorm_span_singleton, show ((p : 𝓞 K)) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp,
    Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]

theorem split_of_card (p : ℕ) (hp : p.Prime) {ι : Type} [Fintype ι] (e : ι → HeightOneSpectrum (𝓞 K))
    (he : Function.Injective e) (hmem : ∀ i, (p : 𝓞 K) ∈ (e i).asIdeal)
    (hcard : Fintype.card ι = Module.finrank ℚ K) :
    (∀ i, Ideal.absNorm (e i).asIdeal = p) ∧ Ideal.span {(p : 𝓞 K)} = ⨅ i, (e i).asIdeal := by
  classical
  set n := Module.finrank ℚ K
  have hcop : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι), i ≠ j →
      IsCoprime (e i).asIdeal (e j).asIdeal := fun i _ j _ hij =>
    HeightOneSpectrum.isCoprime_of_ne _ _ (fun h => hij (he h))
  have hJ : ∏ i, (e i).asIdeal = ⨅ i, (e i).asIdeal := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop]; simp
  have hle : Ideal.span {(p : 𝓞 K)} ≤ ∏ i, (e i).asIdeal := by
    rw [hJ, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_iInf.2 hmem
  have hdvd_i : ∀ i, Ideal.absNorm (e i).asIdeal ∣ p ^ n := fun i => by
    rw [← absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 (hmem i))
  choose k hkn hk using fun i => (Nat.dvd_prime_pow hp).1 (hdvd_i i)
  have hk1 : ∀ i, 1 ≤ k i := fun i => by
    rcases Nat.eq_zero_or_pos (k i) with h | h
    · exfalso
      have h1 := hk i
      rw [h, pow_zero, Ideal.absNorm_eq_one_iff] at h1
      exact (e i).isPrime.ne_top h1
    · exact h
  have hprod : Ideal.absNorm (∏ i, (e i).asIdeal) = p ^ ∑ i, k i := by
    rw [map_prod, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => hk i
  have hsum_le : ∑ i, k i ≤ n := by
    have h := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [hprod, absNorm_span_natCast] at h
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h
  have hsum_eq : ∑ i, k i = ∑ _i : ι, 1 := by
    refine le_antisymm ?_ (Finset.sum_le_sum fun i _ => hk1 i)
    simpa [hcard] using hsum_le
  have hkeq : ∀ i, k i = 1 := fun i =>
    ((Finset.sum_eq_sum_iff_of_le (fun j _ => hk1 j)).1 hsum_eq.symm i (Finset.mem_univ i)).symm
  refine ⟨fun i => by rw [hk i, hkeq i, pow_one], ?_⟩
  rw [← hJ]
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.2 hle
  have hnL : Ideal.absNorm L = 1 := by
    have h := congrArg Ideal.absNorm hL
    rw [map_mul, hprod, absNorm_span_natCast, show ∑ i, k i = n by simpa [hcard] using hsum_eq] at h
    have hpn : 0 < p ^ n := pow_pos hp.pos n
    exact Nat.eq_of_mul_eq_mul_left hpn (by rw [mul_one]; exact h.symm)
  rw [hL, Ideal.absNorm_eq_one_iff.1 hnL, Ideal.mul_top]

theorem trace_pi {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)]
    [∀ i, Module.Finite R (A i)] (z : ∀ i, A i) :
    Algebra.trace R (∀ i, A i) z = ∑ i, Algebra.trace R (A i) (z i) := by
  classical
  let b := fun i => Module.Free.chooseBasis R (A i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (b i), Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr]
  rw [show z * Pi.single i (b i k) = Pi.single i (z i * b i k) by
    funext j; by_cases h : j = i
    · subst h; simp
    · simp [h]]
  simp

theorem intTrace_modEq_sum : ∀ {K : Type} [Field K] [NumberField K] (p : ℕ), p.Prime → ∀ {ι : Type} [Fintype ι] (e : ι → HeightOneSpectrum (𝓞 K)), Function.Injective e → (∀ W : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ W.asIdeal ↔ ∃ i, e i = W) → Fintype.card ι = Module.finrank ℚ K → ∀ (x : 𝓞 K) (b : ι → ℤ), (∀ i, x - (b i : 𝓞 K) ∈ (e i).asIdeal) → ((Algebra.intTrace ℤ (𝓞 K) x : ℤ) : ZMod p) = ∑ i, (b i : ZMod p) := by
  intro K _ _ p hp ι _ e he hW hcard x b hxb
  classical
  have hmem : ∀ i, (p : 𝓞 K) ∈ (e i).asIdeal := fun i => (hW (e i)).2 ⟨i, rfl⟩
  obtain ⟨hnorm, hspan⟩ := split_of_card p hp e he hmem hcard
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  haveI hPm : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  letI := Ideal.Quotient.field P
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) P = ⨅ i, (e i).asIdeal := by
    rw [hPdef, Ideal.map_span, Set.image_singleton, map_natCast]; exact hspan
  have hPv : ∀ i, P ≤ (e i).asIdeal.comap (algebraMap ℤ (𝓞 K)) := fun i => by
    rw [← Ideal.map_le_iff_le_comap, hmap]; exact iInf_le _ i
  letI : ∀ i, Algebra (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) := fun i => Ideal.Quotient.algebraQuotientOfLEComap (hPv i)
  haveI : ∀ i, IsScalarTower ℤ (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) := fun i => .of_algebraMap_eq' rfl
  haveI : ∀ i, Module.Finite (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) := fun i => Module.Finite.of_restrictScalars_finite ℤ _ _
  letI : ∀ i, Field (𝓞 K ⧸ (e i).asIdeal) := fun i => Ideal.Quotient.field _
  have hcop : Pairwise (Function.onFun IsCoprime fun i => (e i).asIdeal) := fun i j hij =>
    HeightOneSpectrum.isCoprime_of_ne _ _ (fun h => hij (he h))
  let φ : (𝓞 K ⧸ Ideal.map (algebraMap ℤ (𝓞 K)) P) ≃ₐ[ℤ ⧸ P] (∀ i, 𝓞 K ⧸ (e i).asIdeal) :=
    { __ := (Ideal.quotEquivOfEq hmap).trans (Ideal.quotientInfRingEquivPiQuotient _ hcop),
      commutes' := Quotient.ind fun _ ↦ rfl }
  have hφ : φ (Ideal.Quotient.mk _ x) = fun i => Ideal.Quotient.mk (e i).asIdeal x := rfl
  have hx1 : ∀ i, Ideal.Quotient.mk (e i).asIdeal x =
      algebraMap (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) (Ideal.Quotient.mk P (b i)) := fun i => by
    rw [Ideal.Quotient.eq.mpr (hxb i)]
    show _ = Ideal.Quotient.mk (e i).asIdeal (algebraMap ℤ (𝓞 K) (b i))
    rw [algebraMap_int_eq, eq_intCast]
  have hcardP : Nat.card (ℤ ⧸ P) = p := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hfr : ∀ i, Module.finrank (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) = 1 := fun i => by
    have hcardv : Nat.card (𝓞 K ⧸ (e i).asIdeal) = p := by
      rw [← hnorm i, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h := Module.natCard_eq_pow_finrank (K := ℤ ⧸ P) (V := 𝓞 K ⧸ (e i).asIdeal)
    rw [hcardP, hcardv] at h
    exact (Nat.pow_right_injective hp.two_le (h.symm.trans (pow_one p).symm))
  have key : Ideal.Quotient.mk P (Algebra.intTrace ℤ (𝓞 K) x) = Ideal.Quotient.mk P (∑ i, b i) := by
    rw [← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv φ, hφ, trace_pi]
    simp_rw [hx1, Algebra.trace_algebraMap, hfr, one_smul]
    rw [map_sum]
  rw [Ideal.Quotient.eq, hPdef, Ideal.mem_span_singleton] at key
  rw [← Int.cast_sum, ZMod.intCast_eq_intCast_iff_dvd_sub]
  obtain ⟨m, hm⟩ := key
  exact ⟨-m, by linear_combination -hm⟩

end GlobalTheory.SplitTrace
