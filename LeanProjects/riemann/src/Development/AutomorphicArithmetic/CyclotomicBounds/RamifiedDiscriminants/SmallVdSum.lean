import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
import Development.AutomorphicArithmetic.CMTraceForms.CmDatumDiscriminantDepthBounds

open NumberField Formalism.HC

theorem UpperTheory.KR.small_vd_sum :
    ∀ {φ : Frame} (H : HostAx φ), (∑ p ∈ H.small, (1 + H.vdH p / 2) * Real.log p ≤ 3 / 2 * Real.logb 2 H.QS) ∧ 2 ∈ H.small ∧
      ∀ r : ℕ, r.Prime → r ∉ H.small → r ≠ H.q → r ≠ H.d → ¬ (r : ℤ) ∣ discr H.E := by
  intro φ H
  obtain ⟨hsm, -, -, -, -⟩ := UpperTheory.cmDatum_discriminantDepth_bounds H
  refine ⟨?_, H.two_mem_small, ?_⟩
  · have hQ0 : H.QS ≠ 0 := H.QS_ne_zero
    have hlogQ : Real.log (H.QS : ℝ) = ∑ p ∈ H.small, (padicValNat p H.QS : ℝ) * Real.log p := by
      show _ = ∑ p ∈ H.QS.primeFactors, (padicValNat p H.QS : ℝ) * Real.log p
      have hprod : (H.QS : ℝ) = ∏ p ∈ H.QS.primeFactors, (p : ℝ) ^ (H.QS.factorization p) := by
        conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hQ0]
        rw [Finsupp.prod, Nat.support_factorization]
        push_cast
        rfl
      rw [hprod, Real.log_prod]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [Real.log_pow, Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]
      · intro p hp
        exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)
    have hlog2 : Real.log (H.QS : ℝ) ≤ Real.logb 2 H.QS := by
      rw [Real.logb]
      have hl0 : 0 ≤ Real.log (H.QS : ℝ) := Real.log_natCast_nonneg _
      have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h2' : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9
        linarith
      rw [le_div_iff₀ h2]
      nlinarith
    calc ∑ p ∈ H.small, (1 + H.vdH p / 2) * Real.log p
        ≤ ∑ p ∈ H.small, 3 / 2 * ((padicValNat p H.QS : ℝ) * Real.log p) := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨hpp, hpd⟩ := (H.mem_small_iff).mp hp
          haveI := Fact.mk hpp
          have hv1 : (1 : ℝ) ≤ padicValNat p H.QS := by
            exact_mod_cast one_le_padicValNat_of_dvd hQ0 hpd
          have hvd := (hsm p hp).1
          have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 2 * padicValNat p H.QS - 1 - H.vdH p / 2) hlp]
      _ = 3 / 2 * Real.log H.QS := by rw [hlogQ, Finset.mul_sum]
      _ ≤ 3 / 2 * Real.logb 2 H.QS := by linarith
  · intro r hr hrs hrq hrd hdvd
    have h : r ∣ H.QS * H.q * H.d := (H.der.discr_primes).1 r hr hdvd
    rcases (Nat.Prime.dvd_mul hr).mp h with h1 | h1
    · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
      · exact hrs ((H.mem_small_iff).mpr ⟨hr, h2⟩)
      · exact hrq ((Nat.prime_dvd_prime_iff_eq hr H.q_prime).mp h2)
    · exact hrd ((Nat.prime_dvd_prime_iff_eq hr H.d_prime).mp h1)
