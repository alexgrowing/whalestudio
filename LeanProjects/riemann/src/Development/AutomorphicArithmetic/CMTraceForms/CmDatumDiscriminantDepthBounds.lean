import Mathlib
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
import Development.AutomorphicArithmetic.FrobeniusLocalisation.VdLe
import Development.AutomorphicArithmetic.FrobeniusLocalisation.inertQ
import Development.AutomorphicArithmetic.FrobeniusLocalisation.InertD

open UpperTheory.HF

open NumberField Formalism.HC

theorem UpperTheory.cmDatum_discriminantDepth_bounds :
    ∀ {φ : Frame} (H : HostAx φ), (∀ l ∈ H.small, H.vdH l ≤ (padicValNat l H.QS : ℝ) ∧ (padicValNat l H.QS : ℝ) ≤ Real.logb 2 H.QS) ∧
      H.vdH H.q ≤ 1 / 2 ∧ H.vdH H.d ≤ 1 / 2 ∧ 0 ≤ Real.logb 2 H.QS ∧
      ∀ p : ℕ, H.vdH p = (padicValInt p (discr H.E) : ℝ) / (Module.finrank ℚ H.E : ℝ) := by
  intro φ H
  have hQ : (1 : ℝ) ≤ H.QS := by exact_mod_cast H.QS_pos
  refine ⟨fun l hl => ?_, ?_, (UpperTheory.HF.inert_d H).2.2.1.le, Real.logb_nonneg one_lt_two hQ, fun p => rfl⟩
  · obtain ⟨hp, hd⟩ := H.mem_small_iff.1 hl
    have hq : l ≠ H.q := fun h => H.q_notMem_small (h ▸ hl)
    have hdd : l ≠ H.d := fun h => H.d_notMem_small (h ▸ hl)
    have hle := (UpperTheory.HF.layer_bot H.toHostRaw (j := 0) hp (Nat.zero_le _)).2.2
    have hfac : H.condN.factorization l = padicValNat l H.QS := by
      rw [HostRaw.condN, Nat.factorization_mul (mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero) H.d_prime.ne_zero,
        Nat.factorization_mul H.QS_ne_zero H.q_prime.ne_zero, Finsupp.add_apply, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (n := H.q)
          (fun h => hq ((Nat.prime_dvd_prime_iff_eq hp H.q_prime).1 h)),
        Nat.factorization_eq_zero_of_not_dvd (n := H.d)
          (fun h => hdd ((Nat.prime_dvd_prime_iff_eq hp H.d_prime).1 h)),
        Nat.factorization_def _ hp]
      rfl
    refine ⟨(UpperTheory.HF.vd_le H hp).2.trans (by exact_mod_cast hfac ▸ hle), ?_⟩
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_natCast]
    have h1 : 2 ^ padicValNat l H.QS ≤ H.QS :=
      (Nat.pow_le_pow_left hp.two_le _).trans (Nat.le_of_dvd H.QS_pos pow_padicValNat_dvd)
    exact_mod_cast h1
  · obtain ⟨-, -, h1, h2, -⟩ := UpperTheory.HF.inert_q H
    by_cases h : H.q ∈ H.ram
    · exact (h1 h).2.1.le
    · rw [h2 h]; norm_num
