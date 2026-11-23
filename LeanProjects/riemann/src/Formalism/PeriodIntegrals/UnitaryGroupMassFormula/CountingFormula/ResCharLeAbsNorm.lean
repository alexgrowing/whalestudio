import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensMultOf

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField IsDedekindDomain

set_option linter.style.haveILetI false

section
variable {K : Type} [Field K] [NumberField K]

theorem quot_finite (p : HeightOneSpectrum (𝓞 K)) : Finite (𝓞 K ⧸ p.asIdeal) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ p.ne_bot

def resChar (p : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ p.asIdeal)

theorem resChar_prime (p : HeightOneSpectrum (𝓞 K)) : (resChar p).Prime := by
  haveI := quot_finite p
  haveI := p.isPrime
  exact CharP.char_is_prime (𝓞 K ⧸ p.asIdeal) (ringChar (𝓞 K ⧸ p.asIdeal))

theorem resChar_mem (p : HeightOneSpectrum (𝓞 K)) : ((resChar p : ℕ) : 𝓞 K) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem resChar_le_absNorm (p : HeightOneSpectrum (𝓞 K)) : resChar p ≤ Ideal.absNorm p.asIdeal := by
  haveI := quot_finite p
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hinj := ZMod.castHom_injective (𝓞 K ⧸ p.asIdeal)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_zmod] at this

theorem fiber_card_le (q : ℕ) (hq : q.Prime) (s : Finset (HeightOneSpectrum (𝓞 K))) :
    (s.filter (fun p => resChar p = q)).card ≤ Module.finrank ℚ K := by
  set T := s.filter (fun p => resChar p = q) with hT

  have hdiv : (∏ p ∈ T, p.asIdeal) ∣ Ideal.span {((q : ℕ) : 𝓞 K)} := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro p _ p' _ hne
      rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne p.isMaximal p'.isMaximal
        (fun h => hne (HeightOneSpectrum.ext h))
    · intro p hp
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      have : resChar p = q := (Finset.mem_filter.mp hp).2
      rw [← this]
      exact resChar_mem p
  have hnorm : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 K)}) = q ^ Module.finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have e : ((q : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (q : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]
  have h1 : Ideal.absNorm (∏ p ∈ T, p.asIdeal) ∣ q ^ Module.finrank ℚ K := by
    rw [← hnorm]
    exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdiv)
  have h2 : q ^ T.card ≤ ∏ p ∈ T, Ideal.absNorm p.asIdeal := by
    apply Finset.pow_card_le_prod
    intro p hp
    have : resChar p = q := (Finset.mem_filter.mp hp).2
    rw [← this]
    exact resChar_le_absNorm p
  rw [← map_prod] at h2
  have h3 := le_trans h2 (Nat.le_of_dvd (pow_pos hq.pos _) h1)
  exact (Nat.pow_le_pow_iff_right hq.one_lt).mp h3
end

theorem prime_zeta_two : PrimeZeta2 := by
  intro K _ _
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  refine summable_of_sum_le
    (c := (Module.finrank ℚ K : ℝ) * ∑' n : ℕ, 1 / ((n : ℝ) ^ 2)) (fun p => by positivity) ?_
  intro u

  have step1 : ∑ p ∈ u, 1 / ((p.asIdeal.absNorm : ℝ) ^ 2) ≤ ∑ p ∈ u, 1 / ((resChar p : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro p _
    have hp : (0 : ℝ) < resChar p := by exact_mod_cast (resChar_prime p).pos
    have hle : (resChar p : ℝ) ≤ (p.asIdeal.absNorm : ℝ) := by exact_mod_cast resChar_le_absNorm p
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  calc ∑ p ∈ u, 1 / ((p.asIdeal.absNorm : ℝ) ^ 2)
      ≤ ∑ p ∈ u, 1 / ((resChar p : ℝ) ^ 2) := step1
    _ = ∑ q ∈ u.image resChar, ∑ p ∈ u with resChar p = q, 1 / ((resChar p : ℝ) ^ 2) :=
        by
          rw [Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem _ hp)]
    _ ≤ ∑ q ∈ u.image resChar, (Module.finrank ℚ K : ℝ) * (1 / ((q : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro q _
        rw [Finset.sum_congr rfl (g := fun _ => 1 / ((q : ℝ) ^ 2))
          (fun p hp => by rw [(Finset.mem_filter.mp hp).2]), Finset.sum_const, nsmul_eq_mul]
        have hc : ((u.filter (fun p => resChar p = q)).card : ℝ) ≤ Module.finrank ℚ K := by
          by_cases hq : q.Prime
          · exact_mod_cast fiber_card_le q hq u
          · have : u.filter (fun p => resChar p = q) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro p _ h
              exact hq (h ▸ resChar_prime p)
            rw [this, Finset.card_empty, Nat.cast_zero]
            positivity
        gcongr
    _ = (Module.finrank ℚ K : ℝ) * ∑ q ∈ u.image resChar, 1 / ((q : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ K : ℝ) * ∑' n : ℕ, 1 / ((n : ℝ) ^ 2) := by
        gcongr
        exact hs.sum_le_tsum _ (fun _ _ => by positivity)

end PI.UnitaryGroupMassFormula.CntFormula
