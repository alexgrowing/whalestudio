import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ExistsHigh

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem eps_num (Sr Yr Y κ lg CM : ℝ) (hY : 1 ≤ Y) (hYr : 0 < Yr) (hS0 : 0 ≤ Sr) (hSY : Sr / Yr ≤ 7 / Y)
    (hκ : 0 < κ) (hlg : 0 ≤ lg) (hlk : 24 * lg ≤ κ) :
    2 * Sr / Yr + (CM * κ + 2 * Sr * lg / Yr) / (Y * κ) ≤ (15 + CM) / Y := by
  have hY0 : 0 < Y := by linarith
  have e1 : (CM * κ + 2 * Sr * lg / Yr) / (Y * κ) = CM / Y + 2 * (Sr / Yr) * (lg / κ) / Y := by
    field_simp
  rw [e1]
  have h1 : lg / κ ≤ 1 / 24 := by rw [div_le_iff₀ hκ]; linarith
  have h2 : 0 ≤ Sr / Yr := div_nonneg hS0 hYr.le
  have h3 : 0 ≤ lg / κ := div_nonneg hlg hκ.le
  have h4 : 2 * (Sr / Yr) * (lg / κ) ≤ 2 * (7 / Y) * (1 / 24) := by gcongr
  have h5 : 7 / Y ≤ 7 := by rw [div_le_iff₀ hY0]; nlinarith
  have h6 : 2 * (Sr / Yr) * (lg / κ) / Y ≤ 1 / Y := by
    apply div_le_div_of_nonneg_right _ hY0.le
    nlinarith
  have h7 : 2 * Sr / Yr = 2 * (Sr / Yr) := by ring
  rw [h7]
  have h8 : 2 * (Sr / Yr) ≤ 14 / Y := by
    have : 2 * (7 / Y) = 14 / Y := by ring
    linarith
  have e2 : (15 + CM) / Y = 14 / Y + CM / Y + 1 / Y := by ring
  rw [e2]
  linarith

theorem epsilon_bound_M_constant (Sr Yr Y κ lg CM : ℝ) (hCM : 1 ≤ CM) (hY : 1 ≤ Y) (hYr : 0 < Yr) (hS0 : 0 ≤ Sr) (hSY : Sr / Yr ≤ 7 / Y)
    (hκ : 0 < κ) (hlg : 0 ≤ lg) (hlk : 24 * lg ≤ κ) :
    2 * Sr / Yr + (2 * κ + 2 * Sr * lg / Yr) / (Y * κ) ≤ (30 + CM) / Y := by
  refine (eps_num Sr Yr Y κ lg 2 hY hYr hS0 hSY hκ hlg hlk).trans ?_
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

structure EpsFacts (C0 : ℝ) (X : flipOneThree.Inst) : Prop where
  pk : X.L.k ^ 2 * X.L.Y ^ 2 ≤ (X.p : ℝ)
  kYb : X.L.k * X.L.Y ^ 2 * X.L.b' ≤ X.L.a / 2

theorem epsFacts {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 2 ≤ CYb) (hC0 : 1 ≤ C0) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (hS : SegFacts C0 CE1 CE2 X) (hb5 : (X.r : ℝ) + 1 ≤ X.L.b') : EpsFacts C0 X := by
  obtain ⟨h0, -⟩ := hH
  obtain ⟨hY, hpk, ⟨s0, hs0, -⟩, -, -, hN1, -, -, hb0, -, -, -, -, hYb, -, hlog, -⟩ := h0
  have hN : (1 : ℝ) ≤ X.L.N := by
    have : 1 ≤ X.L.TT.card := Finset.card_pos.2 ⟨s0, hs0⟩
    show (1 : ℝ) ≤ (X.L.TT.card : ℝ)
    exact_mod_cast this
  have hr5 := r5 hS
  have hkb := hS.kb
  have ha100 : (100 : ℝ) ≤ X.L.a := by
    have h25 : (25 : ℝ) ≤ ((X.r : ℝ) + 1) * X.L.b' := by nlinarith only [hr5, hb5]
    linarith
  have hloga : 1 ≤ Real.log X.L.a := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hLa : 1 ≤ X.L.La C0 := by
    show 1 ≤ lambdaScale C0 X.L.N1 X.L.a
    unfold lambdaScale
    have h1 : (1 : ℝ) ≤ (X.L.N1 : ℝ) := by exact_mod_cast hN1
    have h2 : (1 : ℝ) ≤ (X.L.N1 : ℝ) ^ 2 := one_le_pow₀ h1
    have h3 := one_le_mul_of_one_le_of_one_le hC0 h2
    exact one_le_mul_of_one_le_of_one_le h3 hloga
  have hYb2 : (2 : ℝ) ≤ X.L.Yb := le_trans hCYb hYb
  refine ⟨hpk, ?_⟩
  have h1 : X.L.k * X.L.Y ^ 2 * X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a * X.L.b' ≤ X.L.a := by
    have := mul_le_mul_of_nonneg_right hlog hb0.le
    rwa [div_mul_cancel₀ _ hb0.ne'] at this
  have hM : 2 ≤ X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a := by
    have h4 : (1 : ℝ) ≤ X.L.N * X.L.La C0 * Real.log X.L.a :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN hLa) hloga
    nlinarith only [hYb2, h4]
  have h3 : 0 ≤ X.L.k * X.L.Y ^ 2 * X.L.b' := by
    have : (0 : ℝ) ≤ X.L.k := by show (0 : ℝ) ≤ (X.L.m : ℝ) + 1; positivity
    have := hb0.le
    positivity
  have e : X.L.k * X.L.Y ^ 2 * X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a * X.L.b' =
      (X.L.k * X.L.Y ^ 2 * X.L.b') * (X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a) := by ring
  rw [e] at h1
  have h5 := mul_le_mul_of_nonneg_left hM h3
  linarith

theorem restTMEps_of (hS : SegFacts C0 CE1 CE2 X) (hE' : (X.r : ℝ) + 1 ≤ X.L.b' → EpsFacts C0 X)
    (hFree : RestFree C0 CE1 CE2 X) (CM : ℝ) (hCM : 1 ≤ CM) : RestTMEps C0 CE1 CE2 X CM := by
  intro dl hdl a ha x hx i
  have hk : X.L.k = (X.r : ℝ) + 1 := rfl
  have hk0 : X.L.k ≠ 0 := by rw [hk]; have := r5 hS; linarith
  have hY0 : X.L.Y ≠ 0 := by have := hS.Y1; linarith
  have hr5 := r5 hS
  have hY := hS.Y1
  have hb0 := hS.hF.b0
  have hP1 : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by exact_mod_cast hS.P1 _
  have hkP : ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ X.L.b' := hS.kP _
  have hb5 : (X.r : ℝ) + 1 ≤ X.L.b' := by
    have := mul_le_mul_of_nonneg_left hP1 (by linarith : (0 : ℝ) ≤ (X.r : ℝ) + 1)
    linarith
  have hkY0 : 0 < X.L.k * X.L.Y := by rw [hk]; exact mul_pos (by linarith) (by linarith)
  have hE := hE' hb5
  have hkYb := hE.kYb
  have h4Y : 4 * X.L.Y ≤ X.L.k * X.L.Y ^ 2 := by rw [hk]; nlinarith only [hr5, hY]
  have hYb' : 4 * X.L.Y * X.L.b' ≤ X.L.a := by
    have := mul_le_mul_of_nonneg_right h4Y hb0.le
    have : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    linarith
  have hroomR : (X.L.a : ℝ) + 2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      X.L.a + X.L.a / (X.L.k * X.L.Y) - 1 := by
    have h1 : (2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) * X.L.k ≤ 3 * X.L.b' := by
      rw [hk]; nlinarith only [hkP, hb5]
    have h2 : 3 * X.L.b' * X.L.Y ≤ X.L.a := by nlinarith only [hYb', hY, hb0]
    have h3 : (2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) ≤ X.L.a / (X.L.k * X.L.Y) := by
      rw [le_div_iff₀ hkY0]
      have : (2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) * (X.L.k * X.L.Y) =
          ((2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) * X.L.k) * X.L.Y := by ring
      rw [this]
      nlinarith only [h1, h2, hY]
    linarith
  have hwin : (X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) - 1 <
      ((⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one ((X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa)
    have := hS.xa0
    linarith
  have hroom : X.L.a + 2 * (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) ≤
      ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ := by
    apply Nat.le_floor
    push_cast
    have := hS.xa0
    linarith
  have hYl := Yl_bound hS hFree hdl ha hx i hroom
  have hYP : X.L.a / (2 * (X.L.k * X.L.Y)) ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    have h1 : 1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ X.L.a / (2 * (X.L.k * X.L.Y)) := by
      rw [le_div_iff₀ (by positivity)]
      have h2 : (1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) * ((X.r : ℝ) + 1) ≤ 2 * X.L.b' := by
        nlinarith only [hkP, hb5]
      rw [hk]
      have : (1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) * (2 * (((X.r : ℝ) + 1) * X.L.Y)) =
          2 * X.L.Y * ((1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) * ((X.r : ℝ) + 1)) := by ring
      rw [this]
      nlinarith only [h2, hYb', hY]
    have h4 : X.L.a / (X.L.k * X.L.Y) = 2 * (X.L.a / (2 * (X.L.k * X.L.Y))) := by field_simp
    linarith
  have ha' := aTopPt_mem ha
  have hx' : x ∈ idx C0 CE1 CE2 X dl (aTopPt C0 CE1 CE2 X dl a) := by
    rw [← hFree dl hdl a ha _ ha']; exact hx
  obtain ⟨hK', -, -⟩ := digits_of_idx hx'
  have hT' := (mem_cbox' ha').1
  have hSB := S_bound hS _ hT' x.1 hK' x.2 i
  have eS : (XMof C0 CE1 CE2 X dl a x.1 x.2).T.S ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies
      (XMof C0 CE1 CE2 X dl a x.1 x.2).T (XMof C0 CE1 CE2 X dl a x.1 x.2).top) i =
      (gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i := by
    rw [setTies_top ha hx]
    rfl
  unfold epsM flipOneThree.InstM.eps flipOneThree.InstM.Si flipOneThree.InstM.LLt
  rw [eS]
  have hp : ((X.r : ℝ) + 1) ^ 2 ≤ (X.p : ℝ) := hS.hF.p_ge
  have hp0 : (0 : ℝ) < X.p := by nlinarith only [hp, hr5]
  have hs : 2 * (X.s : ℝ) + 2 ≤ (X.r : ℝ) := by exact_mod_cast hS.hF.s_le
  have hB2 : 0 < X.L.a / (2 * (X.L.k * X.L.Y)) := by
    have : (0 : ℝ) < X.L.a := by nlinarith only [hYb', hY, hb0]
    positivity
  have hYr0 : (0 : ℝ) < ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) := by
    have h2 := lt_of_lt_of_le hB2 hYP
    exact pos_of_mul_pos_left h2 (by linarith)
  have hB1 : 0 ≤ 5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p) := by
    have : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    positivity
  have hfin : (5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p)) * X.L.Y ≤ 7 * (X.L.a / (2 * (X.L.k * X.L.Y))) := by
    have hq : (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) * (2 * X.L.k * X.L.Y ^ 2) ≤ 4 * X.L.a := by
      have hpk' := hE.pk
      have h1 : (2 * (X.s : ℝ) + 1) ≤ X.L.k := by rw [hk]; linarith
      have e3 : (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) * (2 * X.L.k * X.L.Y ^ 2) =
          4 * X.L.a * ((2 * (X.s : ℝ) + 1) * X.L.k * X.L.Y ^ 2) / X.p := by ring
      rw [e3, div_le_iff₀ hp0]
      have h2 : (2 * (X.s : ℝ) + 1) * X.L.k * X.L.Y ^ 2 ≤ X.L.k ^ 2 * X.L.Y ^ 2 := by
        have : 0 ≤ X.L.k * X.L.Y ^ 2 := by rw [hk]; positivity
        nlinarith only [h1, this]
      have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
      nlinarith only [h2, hpk', ha0]
    have hq2 : 5 / 2 * X.L.b' * (2 * X.L.k * X.L.Y ^ 2) ≤ 5 / 2 * X.L.a := by nlinarith only [hkYb]
    have e4 : (5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p)) * X.L.Y =
        ((5 / 2 * X.L.b' * (2 * X.L.k * X.L.Y ^ 2)) + (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) * (2 * X.L.k * X.L.Y ^ 2)) /
          (2 * (X.L.k * X.L.Y)) := by
      field_simp
    rw [e4, div_le_iff₀ (by positivity)]
    have e5 : 7 * (X.L.a / (2 * (X.L.k * X.L.Y))) * (2 * (X.L.k * X.L.Y)) = 7 * X.L.a := by field_simp
    rw [e5]
    linarith
  have hSY : ((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) /
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) ≤ 7 / X.L.Y := by
    have hPp : (0 : ℝ) < ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by linarith
    rw [div_le_div_iff₀ hYr0 (by linarith)]
    have h1 : ((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) *
        ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) * X.L.Y ≤
        7 * (((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) := by
      have h2 := mul_le_mul_of_nonneg_right hSB (by linarith : (0 : ℝ) ≤ X.L.Y)
      have h3 := mul_le_mul_of_nonneg_left hYP (by norm_num : (0 : ℝ) ≤ 7)
      linarith
    have e : ((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) *
        ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) * X.L.Y =
        (((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) * X.L.Y) *
          ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by ring
    have e2 : 7 * (((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) =
        (7 * ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ)) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
      ring
    rw [e, e2] at h1
    exact le_of_mul_le_mul_right h1 hPp
  have hlg1 : 1 ≤ lgA X.p X.L.a X.r := lgA_ge_one_facts hS.hF
  have hκ : 24 * lgA X.p X.L.a X.r ≤ kapS X := by
    unfold kapS
    have h1 : (2 : ℝ) ≤ (X.r : ℝ) := by linarith
    have h2 : (0 : ℝ) ≤ (X.s : ℝ) := Nat.cast_nonneg _
    have h3 : (4 : ℝ) ≤ (X.r : ℝ) ^ 2 := by nlinarith only [h1]
    have h4 : (6 : ℝ) ≤ 3 * ((X.s : ℝ) + 2) := by linarith
    have h5 : (24 : ℝ) ≤ 3 * ((X.s : ℝ) + 2) * (X.r : ℝ) ^ 2 := by nlinarith only [h3, h4]
    nlinarith only [h5, hlg1]
  exact epsilon_bound_M_constant _ _ X.L.Y (kapS X) (lgA X.p X.L.a X.r) CM hCM hY hYr0 (Nat.cast_nonneg _) hSY (by linarith) (by linarith) hκ

theorem restTMEps_proved {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 2 ≤ CYb) (hC0 : 1 ≤ C0) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (hS : SegFacts C0 CE1 CE2 X) (hFree : RestFree C0 CE1 CE2 X) (CM : ℝ) (hCM : 1 ≤ CM) : RestTMEps C0 CE1 CE2 X CM :=
  restTMEps_of hS (epsFacts hCYb hC0 hH hS) hFree CM hCM

theorem restTM_closed : ∃ CM : ℝ, 1 ≤ CM ∧ ∀ (_D : Formalism.BasicNotions.D7) (C0 CE1 CE2 CYb Cde Ck CD Cb Cc : ℝ) (X : flipOneThree.Inst),
    2 ≤ CYb → 1 ≤ Cb → 0 ≤ CD → 1 ≤ C0 → 0 ≤ CE1 → 0 ≤ CE2 →
      flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → RestTM C0 CE1 CE2 X CM := by
  obtain ⟨CM, hCM, h⟩ := restTM_exists
  refine ⟨CM, hCM, fun D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hYb hCb hCD hC0 hE1 hE2 hH => ?_⟩
  have hS := segFacts hYb hCb hCD hE1 hE2 hH (CE1 := CE1) (CE2 := CE2)
  have hF := restFree_proved hS
  exact h D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hH hF (restTMSize_proved hS hF)
    (restTMEps_proved hYb hC0 hH hS hF CM hCM)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
