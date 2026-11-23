import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.FirstCoefficientLeDiv

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.MainNotions.G.SymmetricFormBlocks

theorem clog_le_lg (p : ℕ) (hp : 1 < p) (x : ℕ) (hx : 2 ≤ x) : (Nat.clog p x : ℝ) ≤ Real.logb p x + 1 := by
  have hpos : 0 < Nat.clog p x := Nat.clog_pos hp (by omega)
  have hk := Nat.pow_pred_clog_lt_self hp (by omega : 1 < x)
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hxR : (0 : ℝ) < x := by positivity
  have h1 : (p : ℝ) ^ (Nat.clog p x).pred < x := by exact_mod_cast hk
  have h2 : ((Nat.clog p x).pred : ℝ) < Real.logb p x := by
    rw [Real.lt_logb_iff_rpow_lt hpR hxR, Real.rpow_natCast]
    exact h1
  have h3 : Nat.clog p x = (Nat.clog p x).pred + 1 := (Nat.succ_pred_eq_of_pos hpos).symm
  rw [h3]
  push_cast
  linarith

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

private theorem twentyfive_le_p_of_segFacts (hS : SegFacts C0 CE1 CE2 X) : (25 : ℝ) ≤ X.L.p := by
  have hm4 : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hS.hF.m4
  nlinarith [hS.hF.p_ge]

theorem lgN_le (hS : SegFacts C0 CE1 CE2 X) : (lgN X.p (aBig X) X.r : ℝ) ≤ lgA X.p X.L.a X.r + 1 := by
  have hF := hS.hF
  have hp25 := twentyfive_le_p_of_segFacts hS
  have hp1 : (1 : ℝ) < X.p := by
    show (1 : ℝ) < X.L.p
    linarith
  have ha1 : (1 : ℝ) ≤ X.L.a := hF.a1
  have ha1N : 1 ≤ X.L.a := by exact_mod_cast hF.a1
  have hm4 : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hs : 2 * (X.s : ℝ) + 2 ≤ X.L.m := by exact_mod_cast hF.s_le
  have hyN : 8 * aBig X + X.r ≠ 0 := by
    apply Nat.pos_iff_ne_zero.mp
    unfold aBig
    have := Nat.mul_pos (by omega : 0 < 3 * X.s + 2) (by omega : 0 < X.L.a)
    omega
  have hpow := Nat.pow_log_le_self X.p hyN
  have hyR : (0 : ℝ) < ((8 * aBig X + X.r : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hyN
  have hlog : ((Nat.log X.p (8 * aBig X + X.r) : ℕ) : ℝ) ≤ Real.logb X.p ((8 * aBig X + X.r : ℕ) : ℝ) := by
    rw [Real.le_logb_iff_rpow_le hp1 hyR, Real.rpow_natCast]
    exact_mod_cast hpow
  have hs0 : (0 : ℝ) ≤ X.s := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
  have hyle : ((8 * aBig X + X.r : ℕ) : ℝ) ≤ (3 * (X.s : ℝ) + 2) * (8 * X.L.a + X.r) := by
    unfold aBig
    push_cast
    nlinarith
  have hA : (0 : ℝ) < 8 * X.L.a + X.r := by linarith
  have hB : (0 : ℝ) < 3 * (X.s : ℝ) + 2 := by linarith
  have h2 : Real.logb X.p ((8 * aBig X + X.r : ℕ) : ℝ)
      ≤ Real.logb X.p ((3 * (X.s : ℝ) + 2) * (8 * X.L.a + X.r)) :=
    Real.logb_le_logb_of_le hp1 hyR hyle
  rw [Real.logb_mul hB.ne' hA.ne'] at h2
  have h3 : Real.logb X.p (3 * (X.s : ℝ) + 2) ≤ 1 := by
    rw [Real.logb_le_iff_le_rpow hp1 hB, Real.rpow_one]
    show 3 * (X.s : ℝ) + 2 ≤ X.L.p
    nlinarith [hF.p_ge]
  unfold lgN lgA
  push_cast
  linarith

theorem initial_point_numeric_bound (t s r L lam : ℝ) (ht0 : 0 ≤ t) (hts : t ≤ s) (hr4 : 4 ≤ r) (hL : L ≤ 2 * lam)
    (hlam : 0 ≤ lam) : ((t + 1) * (r + 1) + ((2 * s + 1 + 1) * r + (t + 1) * 2)) * L + L ≤ 3 * (s + 2) * r ^ 2 * lam := by
  have hs0 : 0 ≤ s := le_trans ht0 hts
  have hC0 : 0 ≤ (t + 1) * (r + 1) + ((2 * s + 1 + 1) * r + (t + 1) * 2) + 1 := by nlinarith
  have key := mul_le_mul_of_nonneg_left hL hC0
  have hcoef : 2 * ((t + 1) * (r + 1) + ((2 * s + 1 + 1) * r + (t + 1) * 2) + 1) ≤ 3 * (s + 2) * r ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hts (by linarith : (0 : ℝ) ≤ r),
      mul_le_mul_of_nonneg_left hr4 (by nlinarith : (0 : ℝ) ≤ (s + 2) * r)]
  nlinarith [mul_le_mul_of_nonneg_right hcoef hlam]

theorem initial_point_nat_cast (p A r N t : ℕ) : (x0N p A r N t : ℝ) =
    (((t : ℝ) + 1) * ((r : ℝ) + 1) + (((N : ℝ) + 1) * (r : ℝ) + ((t : ℝ) + 1) * 2)) * (lgN p A r : ℝ) := by
  unfold x0N; push_cast; ring

private theorem one_le_lgA_of_segFacts (hS : SegFacts C0 CE1 CE2 X) : 1 ≤ lgA X.p X.L.a X.r := by
  have hp25 := twentyfive_le_p_of_segFacts hS
  have hp1 : (1 : ℝ) < X.p := by
    show (1 : ℝ) < X.L.p
    linarith
  have ha1 : (1 : ℝ) ≤ X.L.a := hS.hF.a1
  have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
  unfold lgA
  have : 0 ≤ Real.logb X.p (8 * X.L.a + X.r) := Real.logb_nonneg hp1 (by linarith)
  linarith

theorem hx_inst (hS : SegFacts C0 CE1 CE2 X) :
    (x0N X.p (aBig X) X.r (2 * X.s + 1) (X.S C0 CE1 CE2).t : ℝ) + lgN X.p (aBig X) X.r ≤ kapS X := by
  have hF := hS.hF
  rw [initial_point_nat_cast]
  push_cast
  have hL := lgN_le hS
  have hlam1 := one_le_lgA_of_segFacts hS
  have htN : (X.S C0 CE1 CE2).t ≤ X.s := Nat.sub_le _ _
  have ht : ((X.S C0 CE1 CE2).t : ℝ) ≤ X.s := by exact_mod_cast htN
  have hr4 : (4 : ℝ) ≤ X.r := by exact_mod_cast hF.m4
  have key := initial_point_numeric_bound ((X.S C0 CE1 CE2).t : ℝ) X.s X.r (lgN X.p (aBig X) X.r) (lgA X.p X.L.a X.r)
    (Nat.cast_nonneg _) ht hr4 (by linarith) (by linarith)
  unfold kapS
  linarith

theorem win_facts (hS : SegFacts C0 CE1 CE2 X) :
    (X.L.a : ℝ) / (X.L.k * X.L.Y) ≤ (X.winA.card : ℝ) ∧ X.winA.card ≤ X.L.a + 1 := by
  have hF := hS.hF
  have hmem := a_mem_win hS
  unfold flipOneThree.Inst.winA at hmem ⊢
  rw [Nat.card_Icc]
  have haF := (Finset.mem_Icc.mp hmem).2
  have hlt := Nat.lt_floor_add_one ((X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa)
  have hle : ((⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) : ℝ) ≤ 2 * X.L.a :=
    (Nat.floor_le hF.win0).trans hF.win_le
  have hleN : ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ ≤ 2 * X.L.a := by exact_mod_cast hle
  constructor
  · rw [Nat.cast_sub (by omega)]
    push_cast
    linarith [hS.xa0]
  · omega

theorem q_num (J W a k Y b' p : ℝ) (hY : 1 ≤ Y) (hk : 5 ≤ k) (hb : 0 < b') (hpk : k ^ 2 * Y ^ 2 ≤ p) (hpb : p * b' < a)
    (hJ : J ≤ 5 / 2 * b') (hW : a / (k * Y) ≤ W) : 0 < W ∧ J / W ≤ 1 / (2 * Y) := by
  have hY0 : 0 < Y := by linarith
  have hk0 : 0 < k := by linarith
  have hkY : 0 < k * Y := mul_pos hk0 hY0
  have hp0 : 0 < p := by
    have : 0 < k ^ 2 * Y ^ 2 := by positivity
    linarith
  have ha0 : 0 < a := by
    have := mul_pos hp0 hb
    linarith
  have hW1 : k * Y * b' < a / (k * Y) := by
    rw [lt_div_iff₀ hkY]
    have e : k * Y * b' * (k * Y) = k ^ 2 * Y ^ 2 * b' := by ring
    rw [e]
    have : k ^ 2 * Y ^ 2 * b' ≤ p * b' := mul_le_mul_of_nonneg_right hpk hb.le
    linarith
  have hkYb : 0 < k * Y * b' := by positivity
  have hW0 : 0 < W := by linarith
  refine ⟨hW0, ?_⟩
  rw [div_le_div_iff₀ hW0 (by positivity)]
  have h1 : J * (2 * Y) ≤ 5 * b' * Y := by
    nlinarith [mul_le_mul_of_nonneg_right hJ (by linarith : (0 : ℝ) ≤ 2 * Y)]
  have h2 : 5 * b' * Y ≤ k * Y * b' := by
    nlinarith [mul_le_mul_of_nonneg_right hk (by positivity : (0 : ℝ) ≤ Y * b')]
  linarith

theorem kap_facts (hS : SegFacts C0 CE1 CE2 X) (CM : ℝ) (hCM : 1 ≤ CM) :
    lgA X.p X.L.a X.r ≤ kapS X ∧ 0 < kapS X ∧ kapS X ≤ D1r C0 CE1 CE2 X CM := by
  have hF := hS.hF
  have hlam1 := one_le_lgA_of_segFacts hS
  have hr4 : (4 : ℝ) ≤ X.r := by exact_mod_cast hF.m4
  have hs0 : (0 : ℝ) ≤ X.s := Nat.cast_nonneg _
  have hc : 1 ≤ 3 * ((X.s : ℝ) + 2) * (X.r : ℝ) ^ 2 := by nlinarith
  have hk : lgA X.p X.L.a X.r ≤ kapS X := by
    unfold kapS
    nlinarith
  have hk0 : 0 < kapS X := by linarith
  refine ⟨hk, hk0, ?_⟩
  unfold D1r
  have ht0 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).t : ℝ) := Nat.cast_nonneg _
  have hY := hS.Y1
  have h1 : 0 ≤ X.L.Y * kapS X + CM * kapS X := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < X.L.Y) hk0, mul_pos (by linarith : (0 : ℝ) < CM) hk0]
  nlinarith [mul_nonneg ht0 h1, mul_le_mul_of_nonneg_right hCM hk0.le]

private theorem bPlus_le_five_halves_mul_b' (hS : SegFacts C0 CE1 CE2 X) :
    ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ 5 / 2 * X.L.b' := by
  have hmemT : ∀ x ∈ evenTops X.L.TT, x ∈ X.L.TT := fun x hx => by
    unfold evenTops at hx
    rw [Finset.mem_sort] at hx
    exact (Finset.mem_filter.mp hx).1
  have hmem : segNext X.L.TT X.j ∈ X.L.TT := by
    unfold segNext
    exact hmemT _ (List.get_mem _ _)
  exact hS.hF.bT_le _ hmem

theorem restWinNum_proved (hS : SegFacts C0 CE1 CE2 X) (hpk : X.L.k ^ 2 * X.L.Y ^ 2 ≤ (X.L.p : ℝ)) (CM : ℝ)
    (hCM : 1 ≤ CM) : RestWinNum C0 CE1 CE2 X CM := by
  intro aTop haTop b hK J hJ
  have hF := hS.hF
  have hY1 := hS.Y1
  have hp25 := twentyfive_le_p_of_segFacts hS
  have hp1 : (1 : ℝ) < X.p := by
    show (1 : ℝ) < X.L.p
    linarith
  have hp1N : 1 < X.p := by exact_mod_cast hp1
  have ha1 : (1 : ℝ) ≤ X.L.a := hF.a1
  have ha1N : 1 ≤ X.L.a := by exact_mod_cast hF.a1
  have hm4 : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hk5 : (5 : ℝ) ≤ X.L.k := by
    unfold ColumnSystems.Loc.k
    linarith
  obtain ⟨hlk, hk0, hkD⟩ := kap_facts hS CM hCM
  have hD0 : 0 < D1r C0 CE1 CE2 X CM := lt_of_lt_of_le hk0 hkD
  refine ⟨oplus_le_a hS b aTop hK, mul_nonneg (by linarith) hD0.le, ?_⟩
  obtain ⟨hWlow, hWup⟩ := win_facts hS
  have hJR : (J : ℝ) ≤ 5 / 2 * X.L.b' := (Nat.cast_le.mpr hJ).trans (bPlus_le_five_halves_mul_b' hS)
  have hb0 := hF.b0
  have hblt := hF.b_lt
  have hJa : (J : ℝ) ≤ X.L.a := by nlinarith
  have hJaN : J + 1 ≤ X.L.a + 1 := by
    have : J ≤ X.L.a := by exact_mod_cast hJa
    omega
  refine ⟨Nat.clog X.p (X.L.a + 1), hWup.trans (Nat.le_pow_clog hp1N _),
    hJaN.trans (Nat.le_pow_clog hp1N _), ?_⟩
  obtain ⟨hW0, hqY⟩ := q_num (J : ℝ) (X.winA.card : ℝ) X.L.a X.L.k X.L.Y X.L.b' X.L.p hY1 hk5 hb0 hpk hblt hJR hWlow
  have hq0 : 0 ≤ (J : ℝ) / (X.winA.card : ℝ) := div_nonneg (Nat.cast_nonneg _) hW0.le
  have hh0 : (0 : ℝ) ≤ (Nat.clog X.p (X.L.a + 1) : ℝ) := Nat.cast_nonneg _
  have hhk : (Nat.clog X.p (X.L.a + 1) : ℝ) ≤ kapS X := by
    have h1 := clog_le_lg X.p hp1N (X.L.a + 1) (by omega)
    have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
    have hlog : Real.logb X.p ((X.L.a + 1 : ℕ) : ℝ) ≤ Real.logb X.p (8 * X.L.a + X.r) :=
      Real.logb_le_logb_of_le hp1 (by positivity) (by push_cast; linarith)
    unfold lgA at hlk
    linarith
  have hx := hx_inst hS
  have hfl : ((⌊D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) ≤ D1r C0 CE1 CE2 X CM := Int.floor_le _
  have hE : X.L.Y * D1r C0 CE1 CE2 X CM ≤ ((⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + 1 :=
    (Int.lt_floor_add_one _).le
  have key := eps_num X.L.Y (D1r C0 CE1 CE2 X CM) (kapS X) ((J : ℝ) / (X.winA.card : ℝ))
    (Nat.clog X.p (X.L.a + 1) : ℝ)
    ((x0N X.p (aBig X) X.r (2 * X.s + 1) (X.S C0 CE1 CE2).t : ℝ) + (lgN X.p (aBig X) X.r : ℝ))
    ((⌊D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) (((⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + 1)
    hY1 hk0 hkD hq0 hqY hh0 hhk hx hfl hE
  calc _ = (J : ℝ) / (X.winA.card : ℝ)
        + ((x0N X.p (aBig X) X.r (2 * X.s + 1) (X.S C0 CE1 CE2).t : ℝ) + (lgN X.p (aBig X) X.r : ℝ)
          + ((⌊D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + (J : ℝ) / (X.winA.card : ℝ) * (Nat.clog X.p (X.L.a + 1) : ℝ))
          / (((⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + 1) := by ring
    _ ≤ 5 / X.L.Y := key

end Formalism.MainNotions.G.GramWindowAlt

end
