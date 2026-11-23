import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FourDepthLtConductorOfBounds
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MeanDefs

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def Cst.TM (K : Cst) : ℝ := max K.TLP (max (4 * K.CH + 1) (2 * K.Cm + 24))

theorem TM_pos (K : Cst) : 0 < K.TM :=
  lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 108) (le_trans (le_max_left _ _) (le_max_left _ _)))
    (le_max_left _ _)

theorem two_hundred_le_radius {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) : (200 : ℝ) ≤ X.ar := by
  have := mul_le_mul B.hp25 B.hb8 (by norm_num) (by linarith [B.hp25])
  linarith [B.hpa]

theorem log_round {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) :
    Real.log X.ar ≤ Real.log X.a ∧ Real.log X.a ≤ Real.log X.ar + 1 / 200 := by
  have h200 := two_hundred_le_radius B
  have har : 0 < X.ar := by linarith
  have ha : (0 : ℝ) < X.a := by linarith [B.haa]
  refine ⟨Real.log_le_log har B.haa, ?_⟩
  have h1 : Real.log ((X.a : ℝ) / X.ar) = Real.log X.a - Real.log X.ar := Real.log_div ha.ne' har.ne'
  have h2 := Real.log_le_sub_one_of_pos (div_pos ha har)
  have h3 : (X.a : ℝ) / X.ar - 1 ≤ 1 / 200 := by
    have : (X.a : ℝ) / X.ar ≤ 1 + 1 / 200 := by
      rw [div_le_iff₀ har]
      linarith [B.haa1]
    linarith
  linarith

theorem La_round {K : Cst} (hK : K.Pos) {CH : ℝ} {X : Dat} (B : Base K CH X) :
    LaI K.C₀ X.N₁ X.ar ≤ LaI K.C₀ X.N₁ X.a ∧ LaI K.C₀ X.N₁ X.a ≤ 2 * LaI K.C₀ X.N₁ X.ar ∧
      LaI K.C₀ X.N₁ X.a * Real.log X.a ≤ 2 * (LaI K.C₀ X.N₁ X.ar * Real.log X.ar) := by
  obtain ⟨h1, h2⟩ := log_round B
  have hl := B.hlog1
  have hC0 : 0 < K.C₀ := hK.1
  have hcn : 0 ≤ K.C₀ * (X.N₁ : ℝ) ^ 2 := by positivity
  unfold LaI
  refine ⟨mul_le_mul_of_nonneg_left h1 hcn, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left (by linarith : Real.log X.a ≤ 2 * Real.log X.ar) hcn
    linarith
  · have hsq : Real.log X.a * Real.log X.a ≤ 2 * (Real.log X.ar * Real.log X.ar) := by
      have a1 : Real.log X.a ≤ (1 + 1 / 200) * Real.log X.ar := by linarith
      have a0 : 0 ≤ Real.log X.a := by linarith
      have a2 := mul_le_mul a1 a1 a0 (by linarith)
      have a3 : 0 ≤ Real.log X.ar * Real.log X.ar := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_left hsq hcn
    calc K.C₀ * (X.N₁ : ℝ) ^ 2 * Real.log X.a * Real.log X.a
        = K.C₀ * (X.N₁ : ℝ) ^ 2 * (Real.log X.a * Real.log X.a) := by ring
      _ ≤ K.C₀ * (X.N₁ : ℝ) ^ 2 * (2 * (Real.log X.ar * Real.log X.ar)) := this
      _ = _ := by ring

theorem r12 (Yb N La La' b' k w : ℝ) (hYb : 0 ≤ Yb) (hN : 0 ≤ N) (hb : 0 ≤ b') (hk : 0 < k) (h2 : La' ≤ 2 * La)
    (h : Yb * N * La * b' / k ≤ w) : Yb / 2 * N * La' * b' / k ≤ w := by
  have hc : 0 ≤ Yb * N * b' / k := by positivity
  have := mul_le_mul_of_nonneg_left (by linarith : La' / 2 ≤ La) hc
  calc Yb / 2 * N * La' * b' / k = Yb * N * b' / k * (La' / 2) := by ring
    _ ≤ Yb * N * b' / k * La := this
    _ = Yb * N * La * b' / k := by ring
    _ ≤ w := h

theorem r15 (Yb N La La' k : ℝ) (hYb : 0 ≤ Yb) (hN : 0 ≤ N) (h2 : La' ≤ 2 * La) (h : 2 * Yb * N * La < k) :
    2 * (Yb / 2) * N * La' < k := by
  have hc : 0 ≤ Yb * N := by positivity
  have := mul_le_mul_of_nonneg_left h2 hc
  calc 2 * (Yb / 2) * N * La' = Yb * N * La' := by ring
    _ ≤ Yb * N * (2 * La) := this
    _ = 2 * Yb * N * La := by ring
    _ < k := h

theorem r16 (k Y Yb N La La' l l' ar a' b' : ℝ) (hk : 0 ≤ k) (hY : 0 ≤ Y) (hYb : 0 ≤ Yb) (hN : 0 ≤ N) (hb : 0 < b')
    (ha : ar ≤ a') (h2 : La' * l' ≤ 2 * (La * l)) (h : k * Y ^ 2 * Yb * N * La * l ≤ ar / b') :
    k * Y ^ 2 * (Yb / 2) * N * La' * l' ≤ a' / b' := by
  have hc : 0 ≤ k * Y ^ 2 * Yb * N / 2 := by positivity
  have := mul_le_mul_of_nonneg_left h2 hc
  calc k * Y ^ 2 * (Yb / 2) * N * La' * l' = k * Y ^ 2 * Yb * N / 2 * (La' * l') := by ring
    _ ≤ k * Y ^ 2 * Yb * N / 2 * (2 * (La * l)) := this
    _ = k * Y ^ 2 * Yb * N * La * l := by ring
    _ ≤ ar / b' := h
    _ ≤ a' / b' := div_le_div_of_nonneg_right ha hb.le

theorem rde (CH CH1 N1 La La' k r : ℝ) (hCH1 : 0 ≤ CH1) (hCH : 2 * CH1 + 1 ≤ CH) (hN1 : 1 ≤ N1) (hLa : 1 ≤ La)
    (h2 : La' ≤ 2 * La) (hk : 0 < k) : CH1 * N1 * La' / k + r + 1 / k ≤ CH * N1 * La / k + r := by
  have h1 : CH1 * N1 * La' + 1 ≤ CH * N1 * La := by
    have a1 : CH1 * N1 * La' ≤ CH1 * N1 * (2 * La) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have a2 : 1 ≤ N1 * La := one_le_mul_of_one_le_of_one_le hN1 hLa
    have a3 : (2 * CH1 + 1) * (N1 * La) ≤ CH * (N1 * La) := mul_le_mul_of_nonneg_right hCH (by linarith)
    nlinarith
  have := div_le_div_of_nonneg_right h1 hk.le
  have e : (CH1 * N1 * La' + 1) / k = CH1 * N1 * La' / k + 1 / k := add_div _ _ _
  linarith

theorem rband (ar a' b' de de' k x : ℝ) (hb : 0 < b') (hk : 0 < k) (hka : k ≤ ar) (ha : ar ≤ a') (ha1 : a' ≤ ar + 1)
    (hde0 : 0 ≤ de') (hde6 : de' < 1 / 6) (hde : de' + 1 / k ≤ de)
    (h : a' / b' * (1 - 2 * de') ≤ x ∧ x ≤ a' / b' * (1 + 2 * de')) :
    ar / b' * (1 - 2 * de) ≤ x ∧ x ≤ ar / b' * (1 + 2 * de) := by
  have har : 0 < ar := lt_of_lt_of_le hk hka
  have hk1 : 0 < 1 / k := by positivity
  have hab : ar / b' ≤ a' / b' := div_le_div_of_nonneg_right ha hb.le
  have hab0 : 0 ≤ ar / b' := by positivity
  constructor
  · refine le_trans ?_ h.1
    calc ar / b' * (1 - 2 * de) ≤ ar / b' * (1 - 2 * de') := mul_le_mul_of_nonneg_left (by linarith) hab0
      _ ≤ a' / b' * (1 - 2 * de') := mul_le_mul_of_nonneg_right hab (by linarith)
  · refine le_trans h.2 ?_
    have h1 : a' * (1 + 2 * de') ≤ ar * (1 + 2 * de) := by
      have a1 : a' * (1 + 2 * de') ≤ (ar + 1) * (1 + 2 * de') := mul_le_mul_of_nonneg_right ha1 (by linarith)
      have a2 : ar * (1 + 2 * de' + 2 * (1 / k)) ≤ ar * (1 + 2 * de) := mul_le_mul_of_nonneg_left (by linarith) har.le
      have a3 : 1 ≤ ar * (1 / k) := by
        rw [mul_one_div, le_div_iff₀ hk]
        linarith
      nlinarith
    calc a' / b' * (1 + 2 * de') = a' * (1 + 2 * de') / b' := by ring
      _ ≤ ar * (1 + 2 * de) / b' := div_le_div_of_nonneg_right h1 hb.le
      _ = _ := by ring

theorem r19 (CH CH1 N La La' k : ℝ) (hCH1 : 0 ≤ CH1) (hCH : 4 * CH1 ≤ CH) (hN : 0 ≤ N) (hLa0 : 0 ≤ La')
    (h2 : La' ≤ 2 * La) (h : CH * N * La ^ 2 ≤ k) : CH1 * N * La' ^ 2 ≤ k := by
  have a1 : La' ^ 2 ≤ (2 * La) ^ 2 := pow_le_pow_left₀ hLa0 h2 2
  have a2 : CH1 * N * La' ^ 2 ≤ CH1 * N * (2 * La) ^ 2 := mul_le_mul_of_nonneg_left a1 (by positivity)
  have a3 : 4 * CH1 * (N * La ^ 2) ≤ CH * (N * La ^ 2) := mul_le_mul_of_nonneg_right hCH (by positivity)
  calc CH1 * N * La' ^ 2 ≤ CH1 * N * (2 * La) ^ 2 := a2
    _ = 4 * CH1 * (N * La ^ 2) := by ring
    _ ≤ CH * (N * La ^ 2) := a3
    _ = CH * N * La ^ 2 := by ring
    _ ≤ k := h

theorem r22 (CH CH1 G L L' Dp : ℝ) (hCH1 : 0 ≤ CH1) (hCH : 2 * CH1 ≤ CH) (hG : 0 ≤ G) (hL : 0 ≤ L) (h2 : L' ≤ 2 * L)
    (h : CH * G * L ≤ Dp) : CH1 * G * L' ≤ Dp := by
  have a1 : CH1 * G * L' ≤ CH1 * G * (2 * L) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have a2 : 2 * CH1 * (G * L) ≤ CH * (G * L) := mul_le_mul_of_nonneg_right hCH (by positivity)
  calc CH1 * G * L' ≤ CH1 * G * (2 * L) := a1
    _ = 2 * CH1 * (G * L) := by ring
    _ ≤ CH * (G * L) := a2
    _ = CH * G * L := by ring
    _ ≤ Dp := h

theorem hyp_round {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TM ≤ CH) {X : Dat} (h : X.Hyp K.C₀ CH) (B : Base K CH X) :
    HypI K.C₀ K.CH X.p X.n' X.m X.TT X.G' X.N₁ X.Y (X.Yb / 2) (X.a : ℝ) X.b' X.bl X.bu X.ccl X.Dp X.cStar := by
  obtain ⟨hY, hp, hev, hseg2, hgap, hN1, hm, hLa8, hb, hbl, hbu, hIb1, hIb2, hYb, hk2, hab, hde, hpab, hkLa, hband,
    hccl, hD, hcs, hsize⟩ := h
  obtain ⟨l1, l2, l3⟩ := La_round hK B
  obtain ⟨-, -, g3, g4⟩ := logs_of B
  have hCH1 : 0 < K.CH := hK.2.1
  have hCH4 : 4 * K.CH + 1 ≤ CH := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCH
  have h108 : (108 : ℝ) ≤ CH :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hCH
  have hYb0 : 0 ≤ X.Yb := by linarith
  have hN0 : (0 : ℝ) ≤ (X.TT.card : ℝ) := by positivity
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hk0 : (0 : ℝ) < (X.m : ℝ) + 1 := by linarith
  have hLa1 : 1 ≤ LaI K.C₀ X.N₁ X.ar := B.hLa1
  have hLa'0 : 0 ≤ LaI K.C₀ X.N₁ X.a := by linarith
  have hN1r : (1 : ℝ) ≤ (X.N₁ : ℝ) := B.hN1
  have hY0 : 0 ≤ X.Y := by linarith
  have hdd : deI K.CH K.C₀ X.m X.N₁ X.a X.b' X.bl X.bu + 1 / ((X.m : ℝ) + 1) ≤
      deI CH K.C₀ X.m X.N₁ X.ar X.b' X.bl X.bu := by
    unfold deI
    exact rde CH K.CH X.N₁ _ _ _ _ hCH1.le (by linarith) hN1r hLa1 l2 hk0
  have hk1 : 0 < 1 / ((X.m : ℝ) + 1) := by positivity
  have hde0 : 0 ≤ deI K.CH K.C₀ X.m X.N₁ X.a X.b' X.bl X.bu := by
    unfold deI
    have : 0 ≤ X.bu - X.bl := by linarith
    positivity
  have hde6 : deI K.CH K.C₀ X.m X.N₁ X.a X.b' X.bl X.bu < 1 / 6 := by linarith
  have hka : (X.m : ℝ) + 1 ≤ X.ar := by
    have h1 : (X.m : ℝ) + 1 ≤ X.p := B.hkp
    have h2 := le_mul_of_one_le_right (by linarith [B.hp25] : (0 : ℝ) ≤ X.p) (by linarith [B.hb8] : (1 : ℝ) ≤ X.b')
    linarith [B.hpa]
  refine ⟨hY, hp, hev, hseg2, hgap, hN1, hm, by linarith, hb, hbl, hbu, ?_, hIb2, by linarith, ?_, ?_, hde6, ?_, ?_,
    ?_, ?_, ?_, hcs, ?_⟩
  · exact r12 _ _ _ _ _ _ _ hYb0 hN0 hb.le hk0 l2 hIb1
  · exact r15 _ _ _ _ _ hYb0 hN0 l2 hk2
  · exact r16 _ _ _ _ _ _ _ _ _ _ _ hk0.le hY0 hYb0 hN0 hb B.haa l3 hab
  · exact lt_of_lt_of_le hpab (div_le_div_of_nonneg_right B.haa hb.le)
  · exact r19 CH _ _ _ _ _ hCH1.le (by linarith) hN0 hLa'0 l2 hkLa
  · intro d hd hc
    exact hband d hd (rband _ _ _ _ _ _ _ hb hk0 hka B.haa B.haa1.le hde0 hde6 hdd hc)
  · have : LaI K.C₀ X.N₁ X.ar * X.b' / ((X.m : ℝ) + 1) ≤ LaI K.C₀ X.N₁ X.a * X.b' / ((X.m : ℝ) + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right l1 hb.le) hk0.le
    linarith
  · have hG : (0 : ℝ) ≤ (X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3) := by positivity
    have := r22 CH K.CH _ _ _ _ hCH1.le (by linarith) hG (by linarith [B.hL1]) g4
      (by calc CH * ((X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3)) * Real.logb X.p X.ar
            = CH * (X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3) * Real.logb X.p X.ar := by ring
          _ ≤ (X.Dp : ℝ) := hD)
    calc K.CH * (X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3) * Real.logb X.p X.a
        = K.CH * ((X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3)) * Real.logb X.p X.a := by ring
      _ ≤ (X.Dp : ℝ) := this
  · have hG : (0 : ℝ) ≤ ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
        ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y := by positivity
    have := mul_le_mul_of_nonneg_right (by linarith : K.CH ≤ CH) hG
    calc K.CH * ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y
        = K.CH * (((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y) := by ring
      _ ≤ CH * (((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y) := this
      _ = CH * ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y := by ring
      _ ≤ X.b' := hsize

end Formalism.MainNotions.flipOneThree.Pf

end
