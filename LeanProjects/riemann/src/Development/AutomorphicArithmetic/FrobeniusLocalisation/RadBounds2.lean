import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.LogRdSum
import Development.AutomorphicArithmetic.FrobeniusLocalisation.MemRam
import Development.AutomorphicArithmetic.FrobeniusLocalisation.RadBounds
import Development.AutomorphicArithmetic.FrobeniusLocalisation.NormDiffEK
import Development.AutomorphicArithmetic.FrobeniusLocalisation.RdLower

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.rad_bounds2 :
    ∀ {φ : Frame} (H : HostAx φ), (∀ α β : ℝ, 0 ≤ α → 0 ≤ β → ∑ l ∈ H.ram, (α * H.vdH l + β) * Real.log l ≤ (α + 2 * β) * Real.log H.rd) ∧ (H.d : ℝ) ≤ H.rd ^ 2 ∧ H.d ^ (2 * φ.ord) ∣ (discr H.E).natAbs ∧ 1 / 2 * Real.log H.d ≤ Real.log H.rd ∧ H.ram.card ≤ H.small.card + 2 ∧ ∀ (M : ℕ) (L : ℝ), 0 < M → 0 ≤ L → Real.log M ≤ 30 * L → Real.log H.rd ≤ L / 100 → ((((discr H.E).natAbs * M).primeFactors.card : ℕ) : ℝ) ≤ 44 * L := by
  intro φ H
  have hd0 : (0:ℝ) < H.d := by exact_mod_cast (HostRaw.d_prime H.toHostRaw).pos
  obtain ⟨h67, hle, h8, -, -⟩ := rd_lower H
  have hsq : 0 < √(H.d:ℝ) := Real.sqrt_pos.2 hd0
  have hrd0 : 0 < H.rd := by linarith
  have hlt : √(H.d:ℝ) < H.rd := by
    have h1 : 1 < H.rd / √(H.d:ℝ) := by linarith
    rwa [lt_div_iff₀ hsq, one_mul] at h1
  have hdrd : (H.d:ℝ) ≤ H.rd ^ 2 := by
    nlinarith [Real.mul_self_sqrt hd0.le, hsq]
  have hlogd : 1 / 2 * Real.log H.d ≤ Real.log H.rd := by
    have h := Real.log_le_log hd0 hdrd
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  refine ⟨?_, hdrd, Dvd.intro_left _ (norm_diff_EK H).1, hlogd, ?_, ?_⟩
  · intro α β hα hβ
    rw [(log_rd_sum H).1, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    have hp : l.Prime := Nat.prime_of_mem_primeFactors hl
    have hv : 1 / 2 ≤ H.vdH l := (mem_ram H hp).2.2.2.1 hl
    have hlog : 0 ≤ Real.log l := Real.log_natCast_nonneg l
    nlinarith [mul_nonneg (mul_nonneg hβ hlog) (by linarith : (0:ℝ) ≤ 2 * H.vdH l - 1)]
  · have hsub : H.ram ⊆ insert H.q (insert H.d H.small) := by
      intro l hl
      have hp : l.Prime := Nat.prime_of_mem_primeFactors hl
      have hN := (log_rd_sum H).2.2.1 hl
      have hdv : l ∣ H.QS * H.q * H.d := Nat.dvd_of_mem_primeFactors hN
      rcases (Nat.Prime.dvd_mul hp).1 hdv with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rw [Finset.mem_insert, Finset.mem_insert]
          right; right
          exact (HostRaw.mem_small_iff H.toHostRaw).2 ⟨hp, h⟩
        · rw [Finset.mem_insert]
          left
          exact (Nat.prime_dvd_prime_iff_eq hp (HostRaw.q_prime H.toHostRaw)).1 h
      · rw [Finset.mem_insert, Finset.mem_insert]
        right; left
        exact (Nat.prime_dvd_prime_iff_eq hp (HostRaw.d_prime H.toHostRaw)).1 h
    calc H.ram.card ≤ (insert H.q (insert H.d H.small)).card := Finset.card_le_card hsub
      _ ≤ (insert H.d H.small).card + 1 := Finset.card_insert_le _ _
      _ ≤ H.small.card + 1 + 1 := by
        have := Finset.card_insert_le H.d H.small
        omega
      _ = H.small.card + 2 := by ring
  · intro M L hM hL hlogM hrdL
    have hlog2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hl2 : (0:ℝ) < Real.log 2 := by linarith
    have hram : (((discr H.E).natAbs.primeFactors.card : ℕ) : ℝ) ≤ 2 * Real.log H.rd / Real.log 2 :=
      (rad_bounds H).2.1
    have hMcard : ((M.primeFactors.card : ℕ) : ℝ) ≤ Real.log M / Real.log 2 := by
      rw [le_div_iff₀ hl2, ← Real.log_pow]
      have h1 : 2 ^ M.primeFactors.card ≤ ∏ p ∈ M.primeFactors, p := by
        calc 2 ^ M.primeFactors.card = ∏ p ∈ M.primeFactors, 2 := by simp
          _ ≤ ∏ p ∈ M.primeFactors, p :=
            Finset.prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      have h2 : ∏ p ∈ M.primeFactors, p ≤ M := Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd M)
      apply Real.log_le_log (by positivity)
      exact_mod_cast h1.trans h2
    by_cases ha : (discr H.E).natAbs = 0
    · rw [ha, zero_mul, Nat.primeFactors_zero, Finset.card_empty]
      push_cast
      linarith
    have hcard : ((((discr H.E).natAbs * M).primeFactors.card : ℕ) : ℝ) ≤
        ((discr H.E).natAbs.primeFactors.card : ℕ) + ((M.primeFactors.card : ℕ) : ℝ) := by
      rw [Nat.primeFactors_mul ha hM.ne']
      exact_mod_cast Finset.card_union_le _ _
    have hsum : 2 * Real.log H.rd / Real.log 2 + Real.log M / Real.log 2 ≤ 44 * L := by
      rw [← add_div, div_le_iff₀ hl2]
      nlinarith [mul_le_mul_of_nonneg_left hlog2.le hL]
    linarith
