import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow

open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory.PlaceSum

variable {K : Type} [Field K] [NumberField K]

theorem liesOver_resChar (la : HeightOneSpectrum (𝓞 K)) :
    la.asIdeal.LiesOver (Ideal.span {((resCharOf la : ℕ) : ℤ)}) := by
  refine ⟨?_⟩
  ext n
  rw [Ideal.mem_span_singleton, Ideal.under_def, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  have h : (Ideal.Quotient.mk la.asIdeal) (algebraMap ℤ (𝓞 K) n) = (n : 𝓞 K ⧸ la.asIdeal) := by simp
  rw [h]
  exact (CharP.intCast_eq_zero_iff (𝓞 K ⧸ la.asIdeal) (ringChar (𝓞 K ⧸ la.asIdeal)) n).symm

theorem span_ne_bot {p : ℕ} (hp : p.Prime) : Ideal.span {(p : ℤ)} ≠ ⊥ := by
  simpa using hp.ne_zero

theorem span_isMaximal {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal :=
  ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
    (Nat.prime_iff_prime_int.mp hp)).isMaximal (span_ne_bot hp)

theorem mem_primesOverFinset {p : ℕ} (hp : p.Prime) (la : HeightOneSpectrum (𝓞 K)) (h : resCharOf la = p) :
    la.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K) := by
  haveI := span_isMaximal hp
  refine (IsDedekindDomain.mem_primesOverFinset_iff (span_ne_bot hp) _).mpr ⟨la.isPrime, ?_⟩
  rw [← h]
  exact liesOver_resChar la

theorem finite_resChar_eq {p : ℕ} (hp : p.Prime) :
    {la : HeightOneSpectrum (𝓞 K) | resCharOf la = p}.Finite := by
  refine Set.Finite.of_finite_image (f := fun la => la.asIdeal) ?_
    (fun a _ b _ h => HeightOneSpectrum.ext h)
  refine (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).finite_toSet.subset ?_
  rintro _ ⟨la, hla, rfl⟩
  exact mem_primesOverFinset hp la hla

set_option linter.deprecated false in

theorem sum_ram_log_le {p : ℕ} (hp : p.Prime) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ la ∈ T, resCharOf la = p) :
    ∑ la ∈ T, (ramOverZ la : ℝ) * Real.log (Ideal.absNorm la.asIdeal) ≤
      (Module.finrank ℚ K : ℝ) * Real.log p := by
  classical
  haveI := span_isMaximal hp
  have hs := Ideal.sum_ramification_inertia (R := ℤ) (𝓞 K) ℚ K (span_ne_bot hp)
  have h1 : ∀ la ∈ T, (ramOverZ la : ℝ) * Real.log (Ideal.absNorm la.asIdeal) =
      ((Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) la.asIdeal *
        Ideal.inertiaDeg' (Ideal.span {(p : ℤ)}) la.asIdeal : ℕ) : ℝ) * Real.log p := by
    intro la hla
    have h := hT la hla
    haveI : la.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by rw [← h]; exact liesOver_resChar la
    rw [Ideal.absNorm_eq_pow_inertiaDeg' la.asIdeal hp, ramOverZ, h]
    push_cast
    rw [Real.log_pow]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
  rw [← Nat.cast_sum, Nat.cast_le, ← hs]
  rw [← Finset.sum_image (s := T) (g := fun la => la.asIdeal)
    (f := fun P : Ideal (𝓞 K) => Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P *
        Ideal.inertiaDeg' (Ideal.span {(p : ℤ)}) P) (fun a _ b _ h => HeightOneSpectrum.ext h)]
  refine Finset.sum_le_sum_of_subset ?_
  intro P hP
  obtain ⟨la, hla, rfl⟩ := Finset.mem_image.1 hP
  exact mem_primesOverFinset hp la (hT la hla)

theorem finsum_le_sum_primes (K : Type) [Field K] [NumberField K] (φ : ℕ → ℝ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hφ : ∀ p, 0 ≤ φ p) (ν : HeightOneSpectrum (𝓞 K) → ℝ) (h0 : ∀ la, 0 ≤ ν la)
    (hle : ∀ la, ν la ≤ (ramOverZ la : ℝ) * φ (resCharOf la)) (hz : ∀ la, resCharOf la ∉ S → ν la = 0) :
    (Function.support ν).Finite ∧
      (∑ᶠ la, |ν la| * (Real.log (Ideal.absNorm la.asIdeal) / Module.finrank ℚ K)) ≤
        ∑ p ∈ S, φ p * Real.log p := by
  classical
  have hsub : Function.support ν ⊆ ⋃ p ∈ S, {la : HeightOneSpectrum (𝓞 K) | resCharOf la = p} := by
    intro la hla
    simp only [Set.mem_iUnion]
    exact ⟨resCharOf la, by by_contra h; exact hla (hz la h), rfl⟩
  have hfin : (Function.support ν).Finite :=
    (Set.Finite.biUnion S.finite_toSet fun p hp => finite_resChar_eq (hS p hp)).subset hsub
  refine ⟨hfin, ?_⟩
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · have hmap : ∀ la ∈ hfin.toFinset, resCharOf la ∈ S := by
      intro la hla
      by_contra h
      exact (hfin.mem_toFinset.1 hla) (hz la h)
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_le_sum fun p hp => ?_
    have hb := sum_ram_log_le (K := K) (hS p hp) (hfin.toFinset.filter fun la => resCharOf la = p)
      (fun la hla => (Finset.mem_filter.1 hla).2)
    calc _ ≤ ∑ la ∈ hfin.toFinset.filter (fun la => resCharOf la = p),
          (φ p / Module.finrank ℚ K) * ((ramOverZ la : ℝ) * Real.log (Ideal.absNorm la.asIdeal)) := by
          refine Finset.sum_le_sum fun la hla => ?_
          have h := (Finset.mem_filter.1 hla).2
          have h2 := hle la
          rw [h] at h2
          rw [abs_of_nonneg (h0 la)]
          have h3 : 0 ≤ Real.log (Ideal.absNorm la.asIdeal) / Module.finrank ℚ K :=
            div_nonneg (Real.log_natCast_nonneg _) hn.le
          refine (mul_le_mul_of_nonneg_right h2 h3).trans (le_of_eq ?_)
          ring
      _ ≤ (φ p / Module.finrank ℚ K) * ((Module.finrank ℚ K : ℝ) * Real.log p) := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left hb (div_nonneg (hφ p) hn.le)
      _ = φ p * Real.log p := by field_simp
  · intro la hla
    rw [Set.Finite.coe_toFinset]
    intro h
    exact hla (by simp [h])

end GlobalTheory.PlaceSum
