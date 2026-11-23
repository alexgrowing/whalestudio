import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.RecordEigenInputs
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem exists_prime_natCast_mem {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ p : ℕ, p.Prime ∧ (p : R) ∈ P := by
  intro n
  induction n using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    exact absurd ((Ideal.eq_top_iff_one P).mpr (by simpa using h)) hP.ne_top
  | prime_mul p a hp ih =>
    intro hpa h
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h | h
    · exact ⟨p, hp, h⟩
    · exact ih (right_ne_zero_of_mul hpa) h

theorem exists_prime_mem_heightOneSpectrum {L : Type} [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 L)) : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ v.asIdeal := by
  have := v.isPrime
  refine exists_prime_natCast_mem v.asIdeal (Ideal.absNorm v.asIdeal) ?_ (Ideal.absNorm_mem _)
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

theorem log_absNorm_heightOneSpectrum_nonneg {L : Type} [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 L)) : 0 ≤ Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  apply Real.log_nonneg
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h

theorem log_absNorm_eq_sum {L : Type} [Field L] [NumberField L] {I : FractionalIdeal (𝓞 L)⁰ L}
    (hI : I ≠ 0) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (hT : ∀ v, FractionalIdeal.count L v I ≠ 0 → v ∈ T) :
    Real.log (FractionalIdeal.absNorm I : ℝ) =
      ∑ v ∈ T, (FractionalIdeal.count L v I : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := L) hI
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_] at hfac
  · have h1 : (FractionalIdeal.absNorm I : ℝ) =
        ∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ) ^ (FractionalIdeal.count L v I) := by
      conv_lhs => rw [← hfac]
      rw [map_prod, Rat.cast_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]
    rw [h1, Real.log_prod]
    · exact Finset.sum_congr rfl fun v _ => Real.log_zpow _ _
    · intro v _
      apply zpow_ne_zero
      rw [Ne, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    apply hT v
    intro h0
    apply hv
    rw [h0, zpow_zero]

theorem log_absNorm_primeFrac (L : Type) [Field L] [NumberField L] (q : ℕ) :
    Real.log (FractionalIdeal.absNorm (primeFrac L q) : ℝ) = Module.finrank ℚ L * Real.log q := by
  rw [primeFrac, FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  push_cast
  rw [Real.log_pow]

theorem NormCountBound.full : NormCountBound.Statement := by
  intro L _ _ 𝔠 𝔇 S a b h𝔠 h𝔇 ha hb hloc
  classical
  have fin : ∀ J : FractionalIdeal (𝓞 L)⁰ L,
      {v : HeightOneSpectrum (𝓞 L) | FractionalIdeal.count L v J ≠ 0}.Finite :=
    fun J => Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors J)
  let P := S.filter Nat.Prime
  let T : Finset (HeightOneSpectrum (𝓞 L)) := (fin 𝔠).toFinset ∪ (fin (𝔇 : FractionalIdeal (𝓞 L)⁰ L)).toFinset ∪
    P.biUnion (fun q => (fin (primeFrac L q)).toFinset)
  have h𝔠T : ∀ v, FractionalIdeal.count L v 𝔠 ≠ 0 → v ∈ T := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_union_left _ ((fin 𝔠).mem_toFinset.mpr hv))
  have h𝔇T : ∀ v, FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) ≠ 0 → v ∈ T := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_union_right _ ((fin _).mem_toFinset.mpr hv))
  have hqT : ∀ q ∈ P, ∀ v, FractionalIdeal.count L v (primeFrac L q) ≠ 0 → v ∈ T := fun q hq v hv =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q, hq, (fin _).mem_toFinset.mpr hv⟩)
  have h𝔠eq := log_absNorm_eq_sum h𝔠 T h𝔠T
  have h𝔇eq := log_absNorm_eq_sum (I := (𝔇 : FractionalIdeal (𝓞 L)⁰ L))
    (by rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact h𝔇) T h𝔇T
  rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] at h𝔇eq
  have hqeq : ∀ q ∈ P, ∑ v ∈ T, (FractionalIdeal.count L v (primeFrac L q) : ℝ) *
      Real.log (Ideal.absNorm v.asIdeal : ℝ) = Module.finrank ℚ L * Real.log q := fun q hq => by
    rw [← log_absNorm_eq_sum (primeFrac_ne_zero L (Finset.mem_filter.mp hq).2) T (hqT q hq),
      log_absNorm_primeFrac]
  have hterm : ∀ q ∈ P, ∀ v : HeightOneSpectrum (𝓞 L),
      0 ≤ a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) := fun q hq v => by
    apply div_nonneg (mul_nonneg ha (by exact_mod_cast FractionalIdeal.count_coe_nonneg L v _))
    have : (1 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_filter.mp hq).2.one_lt.le
    linarith
  have hv : ∀ v : HeightOneSpectrum (𝓞 L), |(FractionalIdeal.count L v 𝔠 : ℝ)| ≤
      ∑ q ∈ P, a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) +
        b * (FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ) := fun v => by
    obtain ⟨p, hp, hpv⟩ := exists_prime_mem_heightOneSpectrum v
    have h1 := hloc p hp v hpv
    have h2 : (if p ∈ S then a * (FractionalIdeal.count L v (primeFrac L p) : ℝ) / ((p : ℝ) - 1) else 0) ≤
        ∑ q ∈ P, a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) := by
      split_ifs with hpS
      · exact Finset.single_le_sum (f := fun q => a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) /
          ((q : ℝ) - 1)) (fun q hq => hterm q hq v) (Finset.mem_filter.mpr ⟨hpS, hp⟩)
      · exact Finset.sum_nonneg fun q hq => hterm q hq v
    linarith
  have hS : ∑ q ∈ P, Real.log q / ((q : ℝ) - 1) ≤ ∑ q ∈ S, Real.log q / ((q : ℝ) - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro q _ _
    rcases q with _ | q
    · simp
    · have : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 q
      exact div_nonneg (Real.log_nonneg this) (by linarith)
  have hfin : (0 : ℝ) ≤ Module.finrank ℚ L := Nat.cast_nonneg _
  calc |Real.log (FractionalIdeal.absNorm 𝔠 : ℝ)|
      = |∑ v ∈ T, (FractionalIdeal.count L v 𝔠 : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)| := by
        rw [h𝔠eq]
    _ ≤ ∑ v ∈ T, |(FractionalIdeal.count L v 𝔠 : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ v ∈ T, |(FractionalIdeal.count L v 𝔠 : ℝ)| * Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
        Finset.sum_congr rfl fun v _ => by
          rw [abs_mul, abs_of_nonneg (log_absNorm_heightOneSpectrum_nonneg v)]
    _ ≤ ∑ v ∈ T, (∑ q ∈ P, a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) +
          b * (FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ)) *
          Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
        Finset.sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_right (hv v) (log_absNorm_heightOneSpectrum_nonneg v)
    _ = ∑ q ∈ P, a / ((q : ℝ) - 1) * ∑ v ∈ T, (FractionalIdeal.count L v (primeFrac L q) : ℝ) *
          Real.log (Ideal.absNorm v.asIdeal : ℝ) +
        b * ∑ v ∈ T, (FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ) *
          Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
        simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        · exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun v _ => by ring
        · exact Finset.sum_congr rfl fun v _ => by ring
    _ = Module.finrank ℚ L * (a * ∑ q ∈ P, Real.log q / ((q : ℝ) - 1)) +
        b * Real.log (Ideal.absNorm 𝔇 : ℝ) := by
        rw [h𝔇eq, Finset.sum_congr rfl fun q hq => by rw [hqeq q hq]]
        congr 1
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by ring
    _ ≤ Module.finrank ℚ L * (a * ∑ q ∈ S, Real.log q / ((q : ℝ) - 1)) +
        b * Real.log (Ideal.absNorm 𝔇 : ℝ) := by
        gcongr

end GroundTheory.Heights₂.Heights.NineStatements
