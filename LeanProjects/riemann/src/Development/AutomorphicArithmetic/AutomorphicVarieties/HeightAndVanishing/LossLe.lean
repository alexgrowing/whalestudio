import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.lossLe :
    ∀ l N n e : ℕ, l.Prime → l ≠ 2 → 2 ≤ N → n ≤ N → 1 ≤ e → lossAll l N n e ≤ (N * e) ^ 6 ∧ LDataCardLeFinrank.nuBound l N e ≤ 2 * N * e := by
  intro l N n e hl hl2 hN hn he
  have hfac : ∀ (p m : ℕ), m.factorization p ≤ m := by
    intro p m
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0]
    · exact (Nat.factorization_lt p h0.ne').le
  have hnu : LDataCardLeFinrank.nuBound l N e ≤ 2 * N * e := by
    unfold LDataCardLeFinrank.nuBound
    have a1 := hfac l N
    have a2 := hfac l e
    split_ifs
    · have : max (N.factorization l) 1 ≤ N.factorization l + 1 := max_le (by omega) (by omega)
      nlinarith
    · exact Nat.zero_le _
  have hk : N.primeFactors.card ≤ N := by
    calc N.primeFactors.card ≤ (Finset.Icc 1 N).card := by
          apply Finset.card_le_card
          intro p hp
          have hp' := Nat.mem_primeFactors.mp hp
          simp only [Finset.mem_Icc]
          exact ⟨hp'.1.one_lt.le, Nat.le_of_dvd (by omega) hp'.2.1⟩
      _ = N := by simp
  have hv : n.factorization l ≤ N := (hfac l n).trans hn
  refine ⟨?_, hnu⟩
  set M := N * e with hM
  have hNM : N ≤ M := Nat.le_mul_of_pos_right N he
  have hM2 : 2 ≤ M := hN.trans hNM
  have hnuM : LDataCardLeFinrank.nuBound l N e ≤ 2 * M := by rw [hM, ← mul_assoc]; exact hnu
  unfold lossAll Chr.loss
  have b1 : (n + n ^ 2) * LDataCardLeFinrank.nuBound l N e ≤ (M + M ^ 2) * (2 * M) := by
    apply Nat.mul_le_mul _ hnuM
    have : n ≤ M := hn.trans hNM
    have : n ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left this 2
    omega
  have b2 : N.primeFactors.card * (n * n.factorization l) ≤ M * (M * M) :=
    Nat.mul_le_mul (hk.trans hNM) (Nat.mul_le_mul (hn.trans hNM) (hv.trans hNM))
  have b3 : N.primeFactors.card * n.factorization l ≤ M * M :=
    Nat.mul_le_mul (hk.trans hNM) (hv.trans hNM)
  have hM3 : 8 ≤ M ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ M ^ 3 := Nat.pow_le_pow_left hM2 3
  have b4 : (M + M ^ 2) * (2 * M) + M * (M * M) + M * M ≤ M ^ 6 := by
    have e6 : M ^ 6 = M ^ 3 * M ^ 3 := by ring
    have : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h1 : (M + M ^ 2) * (2 * M) + M * (M * M) + M * M = 2 * M ^ 2 + 3 * M ^ 3 + M ^ 2 := by ring
    rw [h1, e6]
    nlinarith
  omega
