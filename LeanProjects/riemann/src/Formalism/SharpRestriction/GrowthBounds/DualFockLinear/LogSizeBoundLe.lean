import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestCloudBOfTwo

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14

theorem num_size2 (C k r N Q cS c0 z Y a : ℝ) (hC : 2 ≤ C) (hk : 1 ≤ k) (hr : 2 ≤ r) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hcS : 8 ≤ cS) (hc0 : 0 ≤ c0) (hz : 0 ≤ z) (hY : 2 ≤ Y)
    (hsz : C * k ^ 3 * r ^ 2 * N * Q ^ 5 * (cS + (r * N * c0 + z)) * Y ≤ a) : 8 * k ≤ a := by
  have hk3 : k ≤ k ^ 3 := le_self_pow₀ hk (by norm_num)
  have hr2 : 4 ≤ r ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hr 2
    norm_num at h
    linarith
  have hQ5 : 1 ≤ Q ^ 5 := one_le_pow₀ hQ
  have hW : 8 ≤ cS + (r * N * c0 + z) := by
    have : 0 ≤ r * N * c0 := by positivity
    linarith
  have hchain : 2 * k * 4 * 1 * 1 * 8 * 2 ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 * (cS + (r * N * c0 + z)) * Y := by
    gcongr
  linarith

theorem log_size_bound_le (p n' m : ℕ) (TT : Finset (Fin n')) (X : Fin n' → Fin (m + 1) → ℤ) (a : ℝ) (hp : 1 < p) (ha : 1 ≤ a)
    (h0 : ∀ s, s ∉ TT → ellWt (lamAt X s) = 0)
    (h1 : ∀ s ∈ TT, ((ellWt (lamAt X s) : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ) ≤ a ^ 2) :
    ((kap1 p X : ℕ) : ℝ) ≤ 2 * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.logb p a := Real.logb_nonneg hp' ha
  unfold kap1
  rw [Nat.cast_sum]
  have hterm : ∀ s, (((if ellWt (lamAt X s) = 0 then 0 else N0 (m + 1) * deF p (m + 1) (ellWt (lamAt X s)) : ℕ)) : ℝ) ≤
      if s ∈ TT then 2 * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a else 0 := by
    intro s
    by_cases hs : s ∈ TT
    · rw [if_pos hs]
      split_ifs with hz
      · rw [Nat.cast_zero]
        exact mul_nonneg (by positivity) hlog
      · rw [Nat.cast_mul]
        have hN0 : ((N0 (m + 1) : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
          have : N0 (m + 1) ≤ (m + 1) ^ 2 := by
            unfold N0
            calc (m + 1) * (m + 1 - 1) / 2 ≤ (m + 1) * (m + 1 - 1) := Nat.div_le_self _ _
              _ ≤ (m + 1) * (m + 1) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
              _ = (m + 1) ^ 2 := by ring
          exact_mod_cast this
        have hde : ((deF p (m + 1) (ellWt (lamAt X s)) : ℕ) : ℝ) ≤ 2 * Real.logb p a := by
          unfold deF
          have hpos : (0 : ℝ) < ((ellWt (lamAt X s) + (m + 1) - 1 : ℕ) : ℝ) := by
            have : 0 < ellWt (lamAt X s) + (m + 1) - 1 := by omega
            exact_mod_cast this
          have hle : ((ellWt (lamAt X s) + (m + 1) - 1 : ℕ) : ℝ) ≤ a ^ 2 := by
            have h2 : ((ellWt (lamAt X s) + (m + 1) - 1 : ℕ) : ℝ) ≤ ((ellWt (lamAt X s) + (m + 1) : ℕ) : ℝ) := by
              exact_mod_cast Nat.sub_le _ _
            have h3 := h1 s hs
            rw [Nat.cast_add] at h2
            linarith
          calc ((Nat.log p (ellWt (lamAt X s) + (m + 1) - 1) : ℕ) : ℝ)
              ≤ Real.logb p ((ellWt (lamAt X s) + (m + 1) - 1 : ℕ) : ℝ) := Real.natLog_le_logb _ _
            _ ≤ Real.logb p (a ^ 2) := Real.logb_le_logb_of_le hp' hpos hle
            _ = 2 * Real.logb p a := by rw [Real.logb_pow]; norm_num
        calc ((N0 (m + 1) : ℕ) : ℝ) * ((deF p (m + 1) (ellWt (lamAt X s)) : ℕ) : ℝ)
            ≤ ((m + 1 : ℕ) : ℝ) ^ 2 * (2 * Real.logb p a) := mul_le_mul hN0 hde (Nat.cast_nonneg _) (by positivity)
          _ = 2 * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a := by ring
    · rw [if_neg hs, if_pos (h0 s hs), Nat.cast_zero]
  calc _ ≤ ∑ s : Fin n', (if s ∈ TT then 2 * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a else 0) :=
        Finset.sum_le_sum fun s _ => hterm s
    _ = _ := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        ring

theorem lastIdx_eq (m : ℕ) : lastIdx (m + 1) = Fin.last m :=
  Fin.ext (by simp [lastIdx])

theorem ellWt_zero (m : ℕ) : ellWt (0 : Fin (m + 1) → ℤ) = 0 := by
  simp [ellWt]

theorem ellWt_flat {n' m : ℕ} (hm : 1 ≤ m) (d : Fin n' → ℕ) (s : Fin n') : ellWt (lamAt (flW (m := m) d) s) = d s := by
  have hne : Fin.last m ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  simp only [lamAt, flW, ellWt, lastIdx_eq]
  split_ifs
  · rw [Pi.single_eq_same, Pi.single_eq_of_ne hne, sub_zero]
    simp
  · simp only [Fin.rev_zero, Fin.rev_last, Pi.single_eq_same, Pi.single_eq_of_ne hne, neg_zero,
      zero_sub, neg_neg]
    simp

theorem sizeStep (C : ℝ) (hC : 2 ≤ C) : SizeStep C 4 := by
  intro p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar H
  have hkc := rank_mul_conductor_div_le_one hC H
  obtain ⟨hp, hr, _, hN1, hW, hY, _, hk, _, hD, hc, hsz⟩ := H
  have hm2 : 2 ≤ m := by omega
  have hN1pos : 1 ≤ orbitWindowCount r de h x := by unfold orbitWindowCount; omega
  have hNnat : 1 ≤ TT.card := by
    rcases Nat.eq_zero_or_pos TT.card with h0' | h0'
    · rw [h0', Nat.mul_zero] at hN1
      have : 0 < orbitWindowCount r de h x ^ 2 := by positivity
      omega
    · exact h0'
  have hN : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hNnat
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have : 1 ≤ m + 1 := by omega
    exact_mod_cast this
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hp1 : (1 : ℝ) < p := by
    have : 1 < p := by omega
    exact_mod_cast this
  have hQ : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := one_le_pow₀ hp1.le
  have hY2 : (2 : ℝ) ≤ Y := le_trans hr2 hY
  have hc0 : (0 : ℝ) ≤ c0 := Nat.cast_nonneg _
  have hz : (0 : ℝ) ≤ 2 * (r : ℝ) * n' * cpp := by positivity
  have hcS : (8 : ℝ) ≤ cStar := by
    have : 8 ≤ cStar := by omega
    exact_mod_cast this
  have h8 := num_size2 C _ _ _ _ _ _ _ Y a hC hk1 hr2 hN hQ hcS hc0 hz hY2 hsz
  have ha8 : 8 ≤ a := by linarith
  have hapos : 0 < a := by linarith
  have hkc' : ((m + 1 : ℕ) : ℝ) * c0 ≤ a := by rwa [div_le_one hapos] at hkc
  have hc0a : (c0 : ℝ) ≤ a := le_trans (le_mul_of_one_le_left hc0 hk1) hkc'
  have hsq : 4 * a ≤ a ^ 2 := by nlinarith
  have A := log_size_bound_le p n' m TT (topW TT lam0) a (by omega) (by linarith)
    (fun s hs => by rw [lamAt_zero (by simp [topW, hs])]; exact ellWt_zero m)
    (fun s hs => by
      rw [lamAt_congr (show topW TT lam0 s = lam0 s by simp [topW, hs])]
      obtain ⟨hb, hdom, hw⟩ := hW
      obtain ⟨e0, elast, _⟩ := (hb s).1 hs
      obtain ⟨w1, w2, hb0, hbc⟩ := hw s hs
      have hzz : lamAt lam0 s 0 - lamAt lam0 s (Fin.last m) = aT s + bT s := by
        unfold lamAt
        split_ifs
        · rw [e0, elast]; ring
        · simp only [Fin.rev_zero, Fin.rev_last]
          rw [e0, elast]; ring
      have haT : 0 ≤ aT s := by
        have : (0 : ℝ) ≤ (aT s : ℝ) := by
          have : (0 : ℝ) ≤ cpp := Nat.cast_nonneg _
          linarith
        exact_mod_cast this
      have e1 : ((ellWt (lamAt lam0 s) : ℕ) : ℝ) = ((aT s + bT s : ℤ) : ℝ) := by
        unfold ellWt
        rw [lastIdx_eq, hzz, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      have hbT : (bT s : ℝ) ≤ c0 := by
        have : bT s ≤ c0 := by omega
        exact_mod_cast this
      have hcp : (0 : ℝ) ≤ cpp := Nat.cast_nonneg _
      rw [e1]
      push_cast
      push_cast at h8
      linarith)
  have B := log_size_bound_le p n' m TT (flW (m := m) (dT TT lam0)) a (by omega) (by linarith)
    (fun s hs => by rw [ellWt_flat (by omega)]; simp [dT, hs])
    (fun s hs => by
      rw [ellWt_flat (by omega)]
      have := (flatDeg_bounds hm2 hapos.le hW s hs).2
      simp only [dT, if_pos hs]
      push_cast
      push_cast at h8
      linarith)
  rw [Nat.cast_add]
  linarith

theorem restSize : RestSize := ⟨4, 2, by norm_num, by norm_num, fun C hC => sizeStep C hC⟩

theorem restCloudB_of_op (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hop : RestTSOp D CLa Ck Crk Cdeg) :
    RestCloudB D CLa Ck Crk Cdeg :=
  restCloudB_of_two D CLa Ck Crk Cdeg hop restSize

end Formalism.MainNotions.TestSideCounting
