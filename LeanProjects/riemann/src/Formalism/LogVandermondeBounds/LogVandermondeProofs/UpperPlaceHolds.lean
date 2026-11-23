import Formalism.LogVandermondeBounds.UpperPlace

namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

lemma up_anti_of_step (f : ℕ → ℝ) (N : ℕ) (h : ∀ i, i + 1 < N → f (i + 1) < f i) :
    ∀ i j, i < j → j < N → f j < f i := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases (show i < j ∨ i = j by omega) with h' | h'
    · exact lt_trans (h j hj) (ih h' (by omega))
    · subst h'; exact h i hj

lemma up_gap_of_step (f : ℕ → ℝ) (N : ℕ) (h : ∀ i, i + 1 < N → 1 ≤ f (i + 1) - f i) :
    ∀ i j, i < j → j < N → 1 ≤ f j - f i := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases (show i < j ∨ i = j by omega) with h' | h'
    · have h1 := h j hj
      have h2 := ih h' (by omega)
      linarith
    · subst h'; exact h i hj

lemma up_vandN_pos (x : ℕ → ℝ) (N : ℕ) (h : ∀ i j, i < j → j < N → x j < x i) :
    0 < vandN x N := by
  unfold vandN
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  rw [Finset.mem_Ico] at hj
  have := h i j (by omega) hj.2
  linarith

lemma up_vand_le (K : ℕ) (u v : ℕ → ℝ) (hint : ∀ i, i < K → v i < u i ∧ u (i + 1) < v i)
    (hu : ∀ i j, i < j → j < K + 1 → 1 ≤ u i - u j)
    (hv : ∀ i j, i < j → j < K → v j < v i) : vandN v K ≤ vandN u (K + 1) := by
  have h1 : vandN v K ≤ ∏ i ∈ range K, ∏ j ∈ Ico (i + 1) K, (u i - u (j + 1)) := by
    unfold vandN
    apply Finset.prod_le_prod
    · intro i hi
      apply Finset.prod_nonneg
      intro j hj
      simp only [mem_Ico, mem_range] at hi hj
      have := hv i j (by omega) hj.2
      linarith
    · intro i hi
      apply Finset.prod_le_prod
      · intro j hj
        simp only [mem_Ico, mem_range] at hi hj
        have := hv i j (by omega) hj.2
        linarith
      · intro j hj
        simp only [mem_Ico, mem_range] at hi hj
        have h1 := (hint i hi).1
        have h2 := (hint j hj.2).2
        linarith
  refine le_trans h1 ?_
  unfold vandN
  rw [Finset.prod_range_succ]
  simp only [Finset.Ico_self, Finset.prod_empty, mul_one]
  apply Finset.prod_le_prod
  · intro i hi
    apply Finset.prod_nonneg
    intro j hj
    simp only [mem_Ico, mem_range] at hi hj
    have := hu i (j + 1) (by omega) (by omega)
    linarith
  · intro i hi
    simp only [mem_range] at hi
    rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : i + 1 < K + 1)]
    rw [← Finset.prod_Ico_add' (fun j => u i - u j) (i + 1) K 1]
    have hrow : 0 ≤ ∏ j ∈ Ico (i + 1) K, (u i - u (j + 1)) := by
      apply Finset.prod_nonneg
      intro j hj
      simp only [mem_Ico] at hj
      have := hu i (j + 1) (by omega) (by omega)
      linarith
    have hgap : 1 ≤ u i - u (i + 1) := hu i (i + 1) (by omega) (by omega)
    have : ∏ j ∈ Ico (i + 1) K, (u i - u (j + 1)) ≤
        (u i - u (i + 1)) * ∏ j ∈ Ico (i + 1) K, (u i - u (j + 1)) := by nlinarith
    simpa using this

lemma up_sign_lo (n i : ℕ) (hi : i < n + 1) : plusSign (n + 2) i = true := by
  unfold plusSign
  exact decide_eq_true (Or.inl (by omega))

lemma up_nB_zero (n a c : ℕ) (hac : a < c) (hc : c < n + 1) : nBetween (n + 2) a c = 0 := by
  unfold nBetween
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  have hx' := Finset.mem_Ioo.mp hx
  rw [up_sign_lo n x (by omega), up_sign_lo n a (by omega)]
  exact fun h => h rfl

lemma up_nB_le (k a c : ℕ) : (nBetween k a c : ℝ) ≤ (c : ℝ) := by
  have h : nBetween k a c ≤ c := by
    unfold nBetween
    calc _ ≤ (Ioo a c).card := Finset.card_filter_le _ _
      _ = c - a - 1 := Nat.card_Ioo a c
      _ ≤ c := by omega
  exact_mod_cast h

private theorem prod_le_pow_of_card_le_of_le (s : Finset ℕ) (G : ℕ → ℝ) (Bd : ℝ) (e : ℕ) (he : s.card ≤ e)
    (hBd : 1 ≤ Bd) (h : ∀ c ∈ s, 0 ≤ G c ∧ G c ≤ Bd) : ∏ c ∈ s, G c ≤ Bd ^ e := by
  calc ∏ c ∈ s, G c ≤ ∏ _c ∈ s, Bd :=
        Finset.prod_le_prod (fun c hc => (h c hc).1) (fun c hc => (h c hc).2)
    _ = Bd ^ s.card := Finset.prod_const Bd
    _ ≤ Bd ^ e := pow_le_pow_right₀ hBd he

lemma up_num_le (n m : ℕ) (lam v : ℕ → ℝ) (Bd : ℝ) (hBd : 1 ≤ Bd)
    (hlamv : ∀ i, i < n + 1 → lam i = v i)
    (hpos : ∀ a c, a < c → c < n + 1 + m → 0 < lam a - lam c + (nBetween (n + 2) a c : ℝ))
    (hle : ∀ a c, a < c → c < n + 1 + m → lam a - lam c + (nBetween (n + 2) a c : ℝ) ≤ Bd) :
    ∏ a ∈ range (n + 1 + m), ∏ c ∈ (Ico (a + 1) (n + 1 + m)).filter
        (fun c => plusSign (n + 2) c = plusSign (n + 2) a),
        (lam a - lam c + (nBetween (n + 2) a c : ℝ))
      ≤ vandN v (n + 1) * Bd ^ (m * (n + 1 + m)) := by
  have hBd0 : 0 ≤ Bd := by linarith
  have hvv : ∀ a c, a < c → c < n + 1 → 0 < v a - v c := by
    intro a c hac hc
    have h1 := hpos a c hac (by omega)
    have h2 : ((nBetween (n + 2) a c : ℕ) : ℝ) = 0 := by
      rw [up_nB_zero n a c hac hc]; simp
    rw [hlamv a (by omega), hlamv c hc, h2] at h1
    linarith
  have rownonneg : ∀ a, 0 ≤ ∏ c ∈ (Ico (a + 1) (n + 1 + m)).filter
      (fun c => plusSign (n + 2) c = plusSign (n + 2) a),
      (lam a - lam c + (nBetween (n + 2) a c : ℝ)) := by
    intro a
    apply Finset.prod_nonneg
    intro c hc
    rw [Finset.mem_filter, Finset.mem_Ico] at hc
    exact (hpos a c (by omega) hc.1.2).le
  have hrow1 : ∀ a, a < n + 1 →
      ∏ c ∈ (Ico (a + 1) (n + 1 + m)).filter (fun c => plusSign (n + 2) c = plusSign (n + 2) a),
        (lam a - lam c + (nBetween (n + 2) a c : ℝ))
      ≤ (∏ c ∈ Ico (a + 1) (n + 1), (v a - v c)) * Bd ^ m := by
    intro a ha
    rw [Finset.prod_filter, ← Finset.prod_Ico_consecutive _ (show a + 1 ≤ n + 1 by omega)
      (show n + 1 ≤ n + 1 + m by omega)]
    apply mul_le_mul
    · apply le_of_eq
      apply Finset.prod_congr rfl
      intro c hc
      rw [Finset.mem_Ico] at hc
      have hcond : plusSign (n + 2) c = plusSign (n + 2) a := by
        rw [up_sign_lo n c (by omega), up_sign_lo n a ha]
      have h2 : ((nBetween (n + 2) a c : ℕ) : ℝ) = 0 := by
        rw [up_nB_zero n a c (by omega) hc.2]; simp
      rw [if_pos hcond, h2, hlamv a ha, hlamv c hc.2]
      ring
    · refine prod_le_pow_of_card_le_of_le _ _ Bd m ?_ hBd ?_
      · rw [Nat.card_Ico]; omega
      · intro c hc
        rw [Finset.mem_Ico] at hc
        split_ifs
        · exact ⟨(hpos a c (by omega) hc.2).le, hle a c (by omega) hc.2⟩
        · exact ⟨zero_le_one, hBd⟩
    · apply Finset.prod_nonneg
      intro c hc
      rw [Finset.mem_Ico] at hc
      split_ifs
      · exact (hpos a c (by omega) hc.2).le
      · exact zero_le_one
    · apply Finset.prod_nonneg
      intro c hc
      rw [Finset.mem_Ico] at hc
      exact (hvv a c (by omega) hc.2).le
  have hrow2 : ∀ a, n + 1 ≤ a →
      ∏ c ∈ (Ico (a + 1) (n + 1 + m)).filter (fun c => plusSign (n + 2) c = plusSign (n + 2) a),
        (lam a - lam c + (nBetween (n + 2) a c : ℝ)) ≤ Bd ^ m := by
    intro a ha
    rw [Finset.prod_filter]
    refine prod_le_pow_of_card_le_of_le _ _ Bd m ?_ hBd ?_
    · rw [Nat.card_Ico]; omega
    · intro c hc
      rw [Finset.mem_Ico] at hc
      split_ifs
      · exact ⟨(hpos a c (by omega) hc.2).le, hle a c (by omega) hc.2⟩
      · exact ⟨zero_le_one, hBd⟩
  rw [Finset.prod_range_add]
  calc _ ≤ (∏ a ∈ range (n + 1), ((∏ c ∈ Ico (a + 1) (n + 1), (v a - v c)) * Bd ^ m)) *
          ∏ _x ∈ range m, Bd ^ m := by
        apply mul_le_mul
        · apply Finset.prod_le_prod
          · intro a _; exact rownonneg a
          · intro a ha; exact hrow1 a (Finset.mem_range.mp ha)
        · apply Finset.prod_le_prod
          · intro x _; exact rownonneg (n + 1 + x)
          · intro x _; exact hrow2 (n + 1 + x) (by omega)
        · exact Finset.prod_nonneg (fun x _ => rownonneg (n + 1 + x))
        · apply Finset.prod_nonneg
          intro a ha
          rw [Finset.mem_range] at ha
          refine mul_nonneg ?_ (pow_nonneg hBd0 m)
          apply Finset.prod_nonneg
          intro c hc
          rw [Finset.mem_Ico] at hc
          exact (hvv a c (by omega) hc.2).le
    _ = vandN v (n + 1) * Bd ^ (m * (n + 1 + m)) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
        unfold vandN
        ring

lemma up_fact_pos (N : ℕ) : 0 < ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ) := by
  apply Finset.prod_pos
  intro i _
  exact Nat.cast_pos.mpr (Nat.factorial_pos i)

lemma up_fact_mono (N P : ℕ) (h : N ≤ P) :
    ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ) ≤ ∏ i ∈ range P, ((i.factorial : ℕ) : ℝ) := by
  induction P, h using Nat.le_induction with
  | base => exact le_refl _
  | succ P _ ih =>
    rw [Finset.prod_range_succ]
    have h0 : 1 ≤ P.factorial := Nat.factorial_pos P
    have h1 : (1 : ℝ) ≤ ((P.factorial : ℕ) : ℝ) := by exact_mod_cast h0
    have h2 : 0 ≤ ∏ i ∈ range P, ((i.factorial : ℕ) : ℝ) := le_of_lt (up_fact_pos P)
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    linarith

private theorem one_le_mul_of_one_le_of_one_le' {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  nlinarith

lemma up_fact_one (N : ℕ) : 1 ≤ ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ]
    have h0 : 1 ≤ N.factorial := Nat.factorial_pos N
    have h1 : (1 : ℝ) ≤ ((N.factorial : ℕ) : ℝ) := by exact_mod_cast h0
    exact one_le_mul_of_one_le_of_one_le' ih h1

lemma up_four_le (n t : ℕ) (ht : 1 ≤ t) : (4 : ℝ) ≤ ((n : ℝ) + 2) * ((t : ℝ) + t) := by
  have h1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

set_option maxHeartbeats 1000000 in
private theorem mul_le_mul_of_one_le {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    a * c ≤ b * d :=
  mul_le_mul hab hcd (by linarith) (by linarith)

private theorem log_four_div_mul_pow_sub_log_le (P Vv Vu Fa Fb F2 Bd Q R : ℝ) (E1 E : ℕ)
    (hP : 0 < P) (hPle : P ≤ Vv * Bd ^ E1) (hVv : 0 < Vv) (hVvu : Vv ≤ Vu)
    (hF2 : 0 < F2) (hF2a : F2 ≤ Fa) (hFb : 1 ≤ Fb) (hBd : 1 ≤ Bd) (hQ : 1 ≤ Q)
    (hR : Real.log 4 + (E1 : ℝ) * Real.log Bd + (E : ℝ) * Real.log Q ≤ R) :
    0 < Vu / F2 ∧ 0 < P / (Fa * Fb) ∧
      Real.log (4 * (P / (Fa * Fb)) * Q ^ E) - Real.log (Vu / F2) ≤ R := by
  have hFa : 0 < Fa := lt_of_lt_of_le hF2 hF2a
  have hFb0 : 0 < Fb := by linarith
  have hVu : 0 < Vu := lt_of_lt_of_le hVv hVvu
  have hBd0 : 0 < Bd := by linarith
  have hQ0 : 0 < Q := by linarith
  have hX : 0 < P / (Fa * Fb) := div_pos hP (mul_pos hFa hFb0)
  refine ⟨div_pos hVu hF2, hX, ?_⟩
  rw [Real.log_mul (mul_pos (by norm_num) hX).ne' (pow_pos hQ0 E).ne',
    Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num) hX.ne',
    Real.log_div hP.ne' (mul_pos hFa hFb0).ne', Real.log_mul hFa.ne' hFb0.ne',
    Real.log_div hVu.ne' hF2.ne', Real.log_pow]
  have h1 : Real.log P ≤ Real.log Vv + (E1 : ℝ) * Real.log Bd := by
    have := Real.log_le_log hP hPle
    rwa [Real.log_mul hVv.ne' (pow_pos hBd0 E1).ne', Real.log_pow] at this
  have h2 := Real.log_le_log hVv hVvu
  have h3 := Real.log_le_log hF2 hF2a
  have h4 := Real.log_nonneg hFb
  linarith

private theorem linear_log_bound_le_K_mul_M (K M L lC l4 lB lQ lK E1 E : ℝ) (hKM : 4 ≤ K * M) (hL : 0 ≤ L)
    (hl4 : l4 ≤ 3) (hl40 : 0 ≤ l4)
    (hE1 : E1 ≤ 2 * (K * M)) (hE : E ≤ K * M)
    (hlB0 : 0 ≤ lB) (hlB : lB ≤ l4 + L + lK)
    (hlQ0 : 0 ≤ lQ) (hlQ : lQ ≤ lC + 3 * lK + l4 + L) :
    l4 + E1 * lB + E * lQ ≤ K * M * (lC + 5 * lK + 5 * L + 10) := by
  have hKM0 : 0 ≤ K * M := by linarith
  have h1 : E1 * lB ≤ 2 * (K * M) * (l4 + L + lK) := mul_le_mul hE1 hlB hlB0 (by linarith)
  have h2 : E * lQ ≤ K * M * (lC + 3 * lK + l4 + L) := mul_le_mul hE hlQ hlQ0 hKM0
  have h3 : K * M * l4 ≤ K * M * 3 := mul_le_mul_of_nonneg_left hl4 hKM0
  have h4 : 0 ≤ K * M * L := mul_nonneg hKM0 hL
  nlinarith

set_option maxHeartbeats 800000 in

theorem UpperPlace_holds : UpperPlace := by
  unfold UpperPlace
  intro ε x hε hx k m Δ C₃ u v b w hm2 hmeven hk2 hmk hΔ hC₃ hI hu
  unfold PlaceData at hI
  obtain ⟨hv0, hvstep, hint_r, -, -, hbw, hbstep, hkb, hwB⟩ := hI
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  obtain ⟨t, rfl⟩ := hmeven
  have e1 : n + 2 - 1 = n + 1 := by omega
  have e2 : (t + t) / 2 = t := by omega
  have ht1 : 1 ≤ t := by omega
  have htn : t + t ≤ n + 2 := by exact_mod_cast hmk
  have hxpos : (0 : ℝ) < x := by linarith
  have hK2 : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n + 2 by omega)
  have hK0 : (0 : ℝ) < 2 * ((n + 2 : ℕ) : ℝ) := by linarith
  have hLnn : 0 ≤ x ^ ε := Real.rpow_nonneg (by linarith) ε
  have hE1 : 1 ≤ Real.exp (x ^ ε) := Real.one_le_exp hLnn
  have hvnn : ∀ i, i < n + 1 → 0 ≤ v i := fun i hi => (hv0 i (by omega)).1
  have hvle : ∀ i, i < n + 1 → v i ≤ ((n + 2 : ℕ) : ℝ) * (4 * Δ) := fun i hi => (hv0 i (by omega)).2
  have hvdec : ∀ i j, i < j → j < n + 1 → v j < v i :=
    up_anti_of_step v (n + 1) (fun i hi => by
      have := hvstep i (by omega)
      linarith)
  have hbinc : ∀ i j, i < j → j < t + t → 1 ≤ b j - b i :=
    up_gap_of_step b (t + t) (fun j hj => (hbstep j hj).2)
  have hbmono : ∀ j, j < t + t → b 0 ≤ b j ∧ b j ≤ b (t + t - 1) := by
    intro j hj
    constructor
    · rcases Nat.eq_zero_or_pos j with h | h
      · subst h; exact le_refl _
      · have := hbinc 0 j h hj; linarith
    · rcases (show j = t + t - 1 ∨ j < t + t - 1 by omega) with h | h
      · subst h; exact le_refl _
      · have := hbinc j (t + t - 1) h (by omega); linarith
  have hb0 : ((n + 2 : ℕ) : ℝ) * (4 * Δ) ≤ b 0 := by
    have h1 := (le_div_iff₀ hxpos).mp hkb
    have h2 : 0 ≤ ((n + 2 : ℕ) : ℝ) * (4 * Δ) := mul_nonneg (by positivity) (by linarith)
    have h3 := mul_le_mul_of_nonneg_left hx h2
    linarith
  have hK8 : (8 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) * (4 * Δ) := by nlinarith
  have hbpos : ∀ j, j < t + t → 8 ≤ b j := by
    intro j hj
    have := (hbmono j hj).1
    linarith
  have hsum : v 0 + b (t + t - 1) ≤ 4 * Real.exp (x ^ ε) := by
    have h1 := hvle 0 (by omega)
    have h2 := (hbmono (t + t - 1) (by omega)).2
    have h3 := (hbmono (t + t - 1) (by omega)).1
    have h4 := (hbw (t + t - 1) (by omega)).1
    linarith
  have hsa : ∀ i, i < n + 1 → rowPar (n + 2) v b i = v i := by
    intro i hi
    show (if i < n + 2 - 1 then v i else -b (i - (n + 2 - 1))) = v i
    rw [e1, if_pos hi]
  have hsb : ∀ i, n + 1 ≤ i → rowPar (n + 2) v b i = -b (i - (n + 1)) := by
    intro i hi
    show (if i < n + 2 - 1 then v i else -b (i - (n + 2 - 1))) = -b (i - (n + 1))
    rw [e1, if_neg (show ¬ i < n + 1 by omega)]
  have hlup : ∀ a, a < n + 1 + (t + t) → rowPar (n + 2) v b a ≤ v 0 := by
    intro a ha
    rcases Nat.lt_or_ge a (n + 1) with h | h
    · rw [hsa a h]
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0; exact le_refl _
      · exact (hvdec 0 a h0 h).le
    · rw [hsb a h]
      have := hbpos (a - (n + 1)) (by omega)
      have := hvnn 0 (by omega)
      linarith
  have hllow : ∀ c, c < n + 1 + (t + t) → -b (t + t - 1) ≤ rowPar (n + 2) v b c := by
    intro c hc
    rcases Nat.lt_or_ge c (n + 1) with h | h
    · rw [hsa c h]
      have := hvnn c h
      have := hbpos (t + t - 1) (by omega)
      linarith
    · rw [hsb c h]
      have := (hbmono (c - (n + 1)) (by omega)).2
      linarith
  have hldec : ∀ a c, a < c → c < n + 1 + (t + t) →
      rowPar (n + 2) v b c < rowPar (n + 2) v b a := by
    intro a c hac hc
    rcases Nat.lt_or_ge c (n + 1) with h | h
    · rw [hsa c h, hsa a (by omega)]
      exact hvdec a c hac h
    · rw [hsb c h]
      rcases Nat.lt_or_ge a (n + 1) with h' | h'
      · rw [hsa a h']
        have := hvnn a h'
        have := hbpos (c - (n + 1)) (by omega)
        linarith
      · rw [hsb a h']
        have := hbinc (a - (n + 1)) (c - (n + 1)) (by omega) (by omega)
        linarith
  obtain ⟨Bd, hBd_def⟩ : ∃ B : ℝ, B = v 0 + b (t + t - 1) + 2 * ((n + 2 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hBd : 1 ≤ Bd := by
    have := hvnn 0 (by omega)
    have := hbpos (t + t - 1) (by omega)
    linarith
  have hpos : ∀ a c, a < c → c < n + 1 + (t + t) →
      0 < rowPar (n + 2) v b a - rowPar (n + 2) v b c + (nBetween (n + 2) a c : ℝ) := by
    intro a c hac hc
    have h1 := hldec a c hac hc
    have h2 : (0 : ℝ) ≤ (nBetween (n + 2) a c : ℝ) := Nat.cast_nonneg _
    linarith
  have hle : ∀ a c, a < c → c < n + 1 + (t + t) →
      rowPar (n + 2) v b a - rowPar (n + 2) v b c + (nBetween (n + 2) a c : ℝ) ≤ Bd := by
    intro a c hac hc
    have h1 := hlup a (by omega)
    have h2 := hllow c hc
    have h3 := up_nB_le (n + 2) a c
    have h4 : (c : ℝ) ≤ 2 * ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show c ≤ 2 * (n + 2) by omega)
    linarith
  have hPle := up_num_le n (t + t) (rowPar (n + 2) v b) v Bd hBd hsa hpos hle
  have hPpos : 0 < ∏ a ∈ range (n + 1 + (t + t)), ∏ c ∈ (Ico (a + 1) (n + 1 + (t + t))).filter
      (fun c => plusSign (n + 2) c = plusSign (n + 2) a),
      (rowPar (n + 2) v b a - rowPar (n + 2) v b c + (nBetween (n + 2) a c : ℝ)) := by
    apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro c hc
    rw [Finset.mem_filter, Finset.mem_Ico] at hc
    exact hpos a c (by omega) hc.1.2
  have hVv : 0 < vandN v (n + 1) := up_vandN_pos v (n + 1) hvdec
  have hVvu : vandN v (n + 1) ≤ vandN u (n + 2) := by
    have h := up_vand_le (n + 1) u v (fun i hi => hint_r i (by omega))
      (fun i j h1 h2 => hu i j h1 (by omega)) hvdec
    rw [show n + 1 + 1 = n + 2 by omega] at h
    exact h
  have hA1 : (1 : ℝ) ≤ ((n + 1 + t : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 + t by omega)
  have hA2 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
  have hA3 : (1 : ℝ) ≤ ((n + 1 + (t + t) : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ n + 1 + (t + t) by omega)
  have hA4 : (1 : ℝ) ≤ v 0 + b (t + t - 1) := by
    have := hvnn 0 (by omega)
    have := hbpos (t + t - 1) (by omega)
    linarith
  have hC0 : 0 < C₃ := by linarith
  have hp1 := one_le_mul_of_one_le_of_one_le' hC₃ hA1
  have hp2 := one_le_mul_of_one_le_of_one_le' hp1 hA2
  have hp3 := one_le_mul_of_one_le_of_one_le' hp2 hA3
  have hQ := one_le_mul_of_one_le_of_one_le' hp3 hA4
  have hB1 : ((n + 1 + t : ℕ) : ℝ) ≤ 2 * ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n + 1 + t ≤ 2 * (n + 2) by omega)
  have hB2 : (t : ℝ) ≤ 2 * ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show t ≤ 2 * (n + 2) by omega)
  have hB3 : ((n + 1 + (t + t) : ℕ) : ℝ) ≤ 2 * ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n + 1 + (t + t) ≤ 2 * (n + 2) by omega)
  have hQle := mul_le_mul_of_one_le (mul_le_mul_of_one_le (mul_le_mul_of_one_le (mul_le_mul_of_one_le le_rfl hB1 hC₃ hA1)
    hB2 hp1 hA2) hB3 hp2 hA3) hsum hp3 hA4
  have hEpos : 0 < 4 * Real.exp (x ^ ε) := by positivity
  have hlQ : Real.log (C₃ * ((n + 1 + t : ℕ) : ℝ) * (t : ℝ) * ((n + 1 + (t + t) : ℕ) : ℝ) *
      (v 0 + b (t + t - 1))) ≤
      Real.log C₃ + 3 * Real.log (2 * ((n + 2 : ℕ) : ℝ)) + Real.log 4 + x ^ ε := by
    have h := Real.log_le_log (by linarith) hQle
    rw [Real.log_mul (mul_pos (mul_pos (mul_pos hC0 hK0) hK0) hK0).ne' hEpos.ne',
      Real.log_mul (mul_pos (mul_pos hC0 hK0) hK0).ne' hK0.ne',
      Real.log_mul (mul_pos hC0 hK0).ne' hK0.ne', Real.log_mul hC0.ne' hK0.ne',
      Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h
    linarith
  have hlB : Real.log Bd ≤ Real.log 4 + x ^ ε + Real.log (2 * ((n + 2 : ℕ) : ℝ)) := by
    have hp : 0 ≤ (4 * Real.exp (x ^ ε) - 2) * (2 * ((n + 2 : ℕ) : ℝ) - 2) :=
      mul_nonneg (by linarith) (by linarith)
    have h1 : Bd ≤ 4 * Real.exp (x ^ ε) * (2 * ((n + 2 : ℕ) : ℝ)) := by nlinarith
    have h2 := Real.log_le_log (by linarith) h1
    rw [Real.log_mul hEpos.ne' hK0.ne', Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num) (Real.exp_pos _).ne',
      Real.log_exp] at h2
    linarith
  have hl4 : Real.log 4 ≤ 3 := by
    have h := Real.add_one_le_exp (3 : ℝ)
    calc Real.log 4 ≤ Real.log (Real.exp 3) := Real.log_le_log (by norm_num) (by linarith)
      _ = 3 := Real.log_exp 3
  have hKM : (4 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) * ((t + t : ℕ) : ℝ) := by
    have := up_four_le n t ht1
    push_cast
    linarith
  have hE1n : (((t + t) * (n + 1 + (t + t)) : ℕ) : ℝ) ≤ 2 * (((n + 2 : ℕ) : ℝ) * ((t + t : ℕ) : ℝ)) := by
    have h : (t + t) * (n + 1 + (t + t)) ≤ 2 * ((n + 2) * (t + t)) := by
      calc (t + t) * (n + 1 + (t + t)) ≤ (t + t) * (2 * (n + 2)) := Nat.mul_le_mul (le_refl _) (by omega)
        _ = 2 * ((n + 2) * (t + t)) := by ring
    exact_mod_cast h
  have hEn : (((n + 1 + t) * t : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) * ((t + t : ℕ) : ℝ) := by
    have h : (n + 1 + t) * t ≤ (n + 2) * (t + t) := by
      calc (n + 1 + t) * t ≤ (2 * (n + 2)) * t := Nat.mul_le_mul (by omega) (le_refl _)
        _ = (n + 2) * (t + t) := by ring
    exact_mod_cast h
  unfold dimVN dTau
  rw [e1, e2]
  refine log_four_div_mul_pow_sub_log_le _ _ _ _ _ _ _ _ _ _ _ hPpos hPle hVv hVvu (up_fact_pos (n + 2))
    (up_fact_mono (n + 2) (n + 1 + t) (by omega)) (up_fact_one t) hBd hQ ?_
  exact linear_log_bound_le_K_mul_M _ _ _ _ _ _ _ _ _ _ hKM hLnn hl4 (Real.log_nonneg (by norm_num)) hE1n hEn
    (Real.log_nonneg hBd) hlB (Real.log_nonneg hQ) hlQ

end Formalism.LogVandermondeBounds.StandardLattice
