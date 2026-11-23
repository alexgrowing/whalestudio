import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.SecondDescentFreePartHolds

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

theorem cost_formula_holds : StatCostFormula := by
  intro ℓ _ hℓ2 j s hjs
  have hℓ : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  have hd : 0 < ℓ - 1 := by omega
  induction s, hjs using Nat.le_induction with
  | base => simp [cost]
  | succ s hjs ih =>
    have hI : Finset.Ioc j (s + 1) = insert (s + 1) (Finset.Ioc j s) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have hnot : s + 1 ∉ Finset.Ioc j s := by simp
    have hc : cost ℓ j (s + 1) =
        cost ℓ j s + (if (ℓ - 1) ∣ (s + 1) then 1 + padicValNat ℓ (s + 1) else 0) := by
      unfold cost
      rw [hI, Finset.sum_insert hnot, add_comm]
    rw [hc]
    by_cases hdv : (ℓ - 1) ∣ (s + 1)
    · rw [if_pos hdv]
      have hq : (s + 1) / (ℓ - 1) = s / (ℓ - 1) + 1 := Nat.succ_div_of_dvd hdv
      have hjq : j / (ℓ - 1) ≤ s / (ℓ - 1) := Nat.div_le_div_right hjs
      have hmul : s + 1 = (ℓ - 1) * (s / (ℓ - 1) + 1) := by
        rw [← hq]
        exact (Nat.mul_div_cancel' hdv).symm
      have hv0 : padicValNat ℓ (ℓ - 1) = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun h => by have := Nat.le_of_dvd hd h; omega)
      have hv : padicValNat ℓ (s + 1) = padicValNat ℓ (s / (ℓ - 1) + 1) := by
        rw [hmul, padicValNat.mul (Nat.pos_iff_ne_zero.1 hd) (Nat.succ_ne_zero _), hv0, zero_add]
      have hf : padicValNat ℓ (s / (ℓ - 1) + 1).factorial =
          padicValNat ℓ (s / (ℓ - 1) + 1) + padicValNat ℓ (s / (ℓ - 1)).factorial := by
        rw [Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _)]
      rw [hq, hv, hf]
      omega
    · rw [if_neg hdv, add_zero, Nat.succ_div_of_not_dvd hdv]
      exact ih

theorem cost_bound : StatCostBound := by
  intro ℓ _ hℓ j s H hjs hsH
  have hprime : ℓ.Prime := Fact.out
  have h3 : 3 ≤ ℓ := by have := hprime.two_le; omega
  have hform := cost_formula_holds ℓ hℓ j s hjs
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hform
  have hL2 : 2 ≤ L := by omega
  set k0 := j / L with hk0
  set k1 := s / L with hk1
  have hk01 : k0 ≤ k1 := Nat.div_le_div_right hjs
  obtain ⟨n', hn'⟩ : ∃ n', k1 = k0 + n' := ⟨k1 - k0, by omega⟩
  have hch := Nat.choose_mul_factorial_mul_factorial hk01
  have hvch : padicValNat (L + 1) k1.factorial = padicValNat (L + 1) (k1.choose k0) +
      padicValNat (L + 1) k0.factorial + padicValNat (L + 1) n'.factorial := by
    rw [← hch, padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos hk01).ne' (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _), padicValNat.mul (Nat.choose_pos hk01).ne' (Nat.factorial_ne_zero _),
      show k1 - k0 = n' by omega]
  have hcost : cost (L + 1) j s = n' + padicValNat (L + 1) n'.factorial +
      padicValNat (L + 1) (k1.choose k0) := by omega
  have hLr : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL2
  have hsub : (((L + 1 : ℕ) : ℝ) - 1) = L := by push_cast; ring
  have hb1 : (1 : ℝ) < ((L + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hHr : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.logb ((L + 1 : ℕ) : ℝ) ((H : ℝ) + 1) := Real.logb_nonneg hb1 (by linarith)
  have hjsr : (j : ℝ) ≤ s := by exact_mod_cast hjs
  rw [hsub]
  have hpos : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  rcases Nat.eq_zero_or_pos n' with h0 | hpos'
  · have : cost (L + 1) j s = 0 := by
      rw [hcost, h0, hn', h0]; simp
    rw [this]
    have : 0 ≤ ((s : ℝ) - j) * ((L + 1 : ℕ) : ℝ) / (L : ℝ) ^ 2 := by
      apply div_nonneg _ hpos.le
      apply mul_nonneg (by linarith) (by linarith)
    push_cast at this hlog0 ⊢
    linarith
  ·
    have hw : L * padicValNat (L + 1) n'.factorial < n' := by
      have := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := L + 1) (n := n') hpos'.ne'
      simpa using this
    have hc : padicValNat (L + 1) (k1.choose k0) ≤ Nat.log (L + 1) k1 := by
      rw [← Nat.factorization_def _ hprime]
      exact Nat.factorization_choose_le_log
    have hk1pos : 1 ≤ k1 := by
      rw [hn']; exact le_trans hpos' (Nat.le_add_left _ _)
    have hk1H : k1 ≤ H := le_trans (Nat.div_le_self _ _) hsH
    have hlog : (Nat.log (L + 1) k1 : ℝ) ≤ Real.logb ((L + 1 : ℕ) : ℝ) ((H : ℝ) + 1) := by
      refine le_trans (Real.natLog_le_logb _ _) ?_
      apply Real.logb_le_logb_of_le hb1
      · exact_mod_cast hk1pos
      · have : (k1 : ℝ) ≤ H := by exact_mod_cast hk1H
        linarith
    have h1 : L * k1 ≤ s := Nat.mul_div_le s L
    have h2 : j < L * k0 + L := by
      have := Nat.lt_mul_div_succ j (show 0 < L by omega)
      rw [← hk0] at this
      nlinarith
    have hA : L * n' + j + 1 ≤ s + L := by
      have : L * k1 = L * k0 + L * n' := by rw [hn']; ring
      omega
    set w := padicValNat (L + 1) n'.factorial with hwdef
    set c := padicValNat (L + 1) (k1.choose k0) with hcdef
    have rA : (L : ℝ) * n' + j + 1 ≤ s + L := by exact_mod_cast hA
    have rB : (L : ℝ) * w + 1 ≤ n' := by exact_mod_cast hw
    have rC : (c : ℝ) ≤ Real.logb ((L + 1 : ℕ) : ℝ) ((H : ℝ) + 1) :=
      le_trans (by exact_mod_cast hc) hlog
    have key : ((n' : ℝ) + w) < ((s : ℝ) - j) * ((L + 1 : ℕ) : ℝ) / (L : ℝ) ^ 2 + 1 := by
      rw [← sub_lt_iff_lt_add, lt_div_iff₀ hpos]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left rA (by linarith : (0 : ℝ) ≤ L),
        mul_le_mul_of_nonneg_left rB (by linarith : (0 : ℝ) ≤ L)]
    rw [hcost]
    push_cast at key rC ⊢
    linarith

theorem unconditional_first_statement : Stat1 := first_descent_of_cost_bound cost_bound

theorem unit_lemma_case_a_unconditional : StatWA := wA_of unconditional_first_statement

end Formalism.RepresentationBoundsCohomology.N2
