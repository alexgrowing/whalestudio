import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Transported

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem numSeg_le_card {n' : ℕ} (TT : Finset (Fin n')) : numSeg TT ≤ TT.card := by
  unfold numSeg evenTops
  rw [Finset.length_sort]
  exact Finset.card_filter_le _ _

theorem error_ratio_le_epsilon {p k N1 La Q c a b' CE1 CE2 : ℝ} (hk : 1 ≤ k) (hp : k ^ 2 ≤ p) (hN1 : 1 ≤ N1) (hLa : 1 ≤ La)
    (hQ : 1 ≤ Q) (_hc : 0 ≤ c) (hb : 0 < b') (hab : k * b' ≤ a) (hHc : k ^ 3 * Q ^ 2 * c ≤ b')
    (hHb : k ^ 3 * Q ≤ b') (h1 : 0 ≤ CE1) (h2 : 0 ≤ CE2) (hk2 : 4 * CE1 + CE2 + 1 ≤ k) :
    errorTermBound CE1 CE2 p k N1 Q c a b' La / a + Q / a ≤ N1 * La / k := by
  have hk0 : 0 < k := by linarith
  have hkne : k ≠ 0 := hk0.ne'
  have hksq : 0 < k ^ 2 := pow_pos hk0 2
  have hkp : k ≤ p := by nlinarith
  have hp0 : 0 < p := by linarith
  have ha : 0 < a := lt_of_lt_of_le (mul_pos hk0 hb) hab
  have hLa0 : 0 ≤ La := by linarith
  have hN10 : 0 ≤ N1 := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hNL : 1 ≤ N1 * La := by nlinarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = N1 * La / k ^ 2 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; exact div_nonneg (by linarith) hksq.le
  have hAk : A * k ^ 2 = N1 * La := by rw [hA]; field_simp
  have hAk' : a * A * k ^ 2 = a * (N1 * La) := by rw [mul_assoc, hAk]
  have haA : 0 ≤ a * A := mul_nonneg ha.le hA0
  have hNLa : a * 1 ≤ a * (N1 * La) := mul_le_mul_of_nonneg_left hNL ha.le
  have hAk1 : b' ≤ a * A * k := by
    have h : k * b' ≤ k * (a * A * k) := by linarith
    exact le_of_mul_le_mul_left h hk0
  have t1 : a / p ^ 2 ≤ a * A := by
    rw [div_le_iff₀ (pow_pos hp0 2)]
    have hkp2 : k ^ 2 ≤ p ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hkp2 haA]
  have t2 : b' / p ≤ a * A := by
    rw [div_le_iff₀ hp0]
    nlinarith [mul_le_mul_of_nonneg_left hkp haA]
  have t3 : La * N1 * a / (p * k) ≤ a * A := by
    rw [div_le_iff₀ (mul_pos hp0 hk0)]
    have hkk : k * k ≤ p * k := mul_le_mul_of_nonneg_right hkp hk0.le
    nlinarith [mul_le_mul_of_nonneg_left hkk haA]
  have t4 : La * b' / k ≤ a * A := by
    rw [div_le_iff₀ hk0]
    have h4a : La * (k * b') ≤ La * a := mul_le_mul_of_nonneg_left hab hLa0
    have h4b : La * a * 1 ≤ La * a * N1 := mul_le_mul_of_nonneg_left hN1 (mul_nonneg hLa0 ha.le)
    have h : k * (La * b') ≤ k * (a * A * k) := by nlinarith
    exact le_of_mul_le_mul_left h hk0
  have t5 : k ^ 2 * N1 * Q ^ 2 * c ≤ a * A := by
    have h5a : k ^ 3 * Q ^ 2 * c * k ≤ b' * k := mul_le_mul_of_nonneg_right hHc hk0.le
    have h5b : a * 1 ≤ a * La := mul_le_mul_of_nonneg_left hLa ha.le
    have h5c : N1 * (k ^ 3 * Q ^ 2 * c * k) ≤ N1 * (a * La) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hN10
    have h : k ^ 2 * (k ^ 2 * N1 * Q ^ 2 * c) ≤ k ^ 2 * (a * A) := by nlinarith
    exact le_of_mul_le_mul_left h hksq
  have t6 : Q ≤ a * A := by
    have h6a : k * (k ^ 3 * Q) ≤ k * b' := mul_le_mul_of_nonneg_left hHb hk0.le
    have hk2ge : 1 ≤ k ^ 2 := by nlinarith
    have h6b : k ^ 2 * 1 ≤ k ^ 2 * k ^ 2 := mul_le_mul_of_nonneg_left hk2ge hksq.le
    have h6c : Q * k ^ 2 ≤ Q * (k ^ 2 * k ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hQ0
    have h : k ^ 2 * Q ≤ k ^ 2 * (a * A) := by nlinarith
    exact le_of_mul_le_mul_left h hksq
  rw [← add_div, div_le_iff₀ ha]
  unfold errorTermBound
  have s1 : CE1 * (a / p ^ 2 + b' / p + La * N1 * a / (p * k) + La * b' / k) ≤ CE1 * (4 * (a * A)) :=
    mul_le_mul_of_nonneg_left (by linarith) h1
  have s2 : CE2 * (k ^ 2 * N1 * Q ^ 2 * c) ≤ CE2 * (a * A) := mul_le_mul_of_nonneg_left t5 h2
  have s3 : (4 * CE1 + CE2 + 1) * (a * A) ≤ k * (a * A) := mul_le_mul_of_nonneg_right hk2 haA
  have s4 : k * (a * A) = N1 * La / k * a := by rw [hA]; field_simp; try ring
  linarith

def T2 (CE1 CE2 Cc H : ℝ) : ℝ := 1000 * (CE1 + CE2 + 1) * (Cc + 1) * H

theorem chordCoeffCubic_inversionDenom_inv {CE1 CE2 Cc H : ℝ} (hCc : 0 ≤ Cc) (h1 : 1 ≤ CE1) (h2 : 1 ≤ CE2) (hH : 1 ≤ H) :
    1000 ≤ T2 CE1 CE2 Cc H ∧ 4 * CE1 + CE2 + 1 ≤ T2 CE1 CE2 Cc H ∧ 2 * Cc * H ≤ T2 CE1 CE2 Cc H ∧
      H ≤ T2 CE1 CE2 Cc H := by
  unfold T2
  have hP : 3 ≤ CE1 + CE2 + 1 := by linarith
  have hM1 : 1 ≤ (Cc + 1) * H := by nlinarith
  have hMH : H ≤ (Cc + 1) * H := by nlinarith
  have hMC : Cc * H ≤ (Cc + 1) * H := by nlinarith
  have hCH : 0 ≤ Cc * H := mul_nonneg hCc (by linarith)
  have ha : (CE1 + CE2 + 1) * 1 ≤ (CE1 + CE2 + 1) * ((Cc + 1) * H) :=
    mul_le_mul_of_nonneg_left hM1 (by linarith)
  have hb : 3 * ((Cc + 1) * H) ≤ (CE1 + CE2 + 1) * ((Cc + 1) * H) :=
    mul_le_mul_of_nonneg_right hP (by linarith)
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

set_option maxHeartbeats 1000000 in
theorem std_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc H : ℝ} (hCc : 0 ≤ Cc) (hC0 : 1 ≤ C0) (h1 : 1 ≤ CE1) (h2 : 1 ≤ CE2)
    (hH : 1 ≤ H) (t1 : T2 CE1 CE2 Cc H ≤ CYb) (t2 : T2 CE1 CE2 Cc H ≤ Cde) (t3 : T2 CE1 CE2 Cc H ≤ Ck)
    (t4 : T2 CE1 CE2 Cc H ≤ CD) (t5 : T2 CE1 CE2 Cc H ≤ Cb) {X : Loc} (hD : D1num X)
    (hI : HIext C0 CYb Cde Ck CD Cb X) (hc : CBound Cc X) : Std C0 Cde CE1 CE2 H X := by
  have om : ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → 1 ≤ x * y := fun x y hx hy => by nlinarith
  obtain ⟨hT1, hT2, hT3, hT4⟩ := chordCoeffCubic_inversionDenom_inv hCc h1 h2 hH
  unfold D1num at hD
  obtain ⟨hpP, hp5, hn2, hnEv⟩ := hD
  unfold HIext WindowHypotheses InWin at hI
  obtain ⟨⟨hY1, hpk, _hEv, hseg, hsegB, hN1, hm, hLaNY, hb, hbl, hbh, _hYbw, _hw2, hCYb, hYbk, hab16,
    hde, hpab, hCk, hband, hccl0, _hccl, hDLP, hcs, hCb⟩, hwA, hwB⟩ := hI
  unfold CBound at hc

  have hkdef : X.k = (X.m : ℝ) + 1 := rfl
  have hmR : 2 * (X.N1 : ℝ) + 2 ≤ X.m := by exact_mod_cast hm
  have hN1R : (1 : ℝ) ≤ X.N1 := by exact_mod_cast hN1
  have sq_level_le_degree : 2 * (X.N1 : ℝ) + 3 ≤ X.k := by rw [hkdef]; linarith
  have hk0 : 0 < X.k := by linarith
  have hkne : X.k ≠ 0 := hk0.ne'
  have hp5R : (5 : ℝ) ≤ X.p := by exact_mod_cast hp5
  have hQdef : X.Q = (X.p : ℝ) ^ X.G' := rfl
  have hQ1 : 1 ≤ X.Q := by rw [hQdef]; exact one_le_pow₀ (by linarith)
  have hQ0 : 0 ≤ X.Q := by linarith
  have hcard : 2 ≤ X.TT.card := le_trans hseg (numSeg_le_card _)
  have hN2 : (2 : ℝ) ≤ X.N := by show (2 : ℝ) ≤ (X.TT.card : ℝ); exact_mod_cast hcard
  have hN0 : (0 : ℝ) ≤ X.N := by linarith
  have hY0 : 0 ≤ X.Y := by linarith
  have hbne : X.b' ≠ 0 := hb.ne'
  have hYb1 : 1 ≤ X.Yb := by linarith
  have hY2 : 1 ≤ X.Y ^ 2 := one_le_pow₀ hY1

  have ha1 : (1 : ℝ) ≤ X.a := by
    have hne : X.a ≠ 0 := by
      intro h
      rw [h, Nat.cast_zero, zero_div] at hpab
      linarith
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  have hlogb : 0 ≤ Real.logb X.p X.a := Real.logb_nonneg (by linarith) ha1
  have hDLP0 : 0 ≤ X.DLP := le_trans (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hN0)
    (sq_nonneg _)) (add_nonneg (pow_nonneg (Nat.cast_nonneg _) 5) (pow_nonneg hk0.le 3))) hlogb) hDLP
  have hNc : 0 ≤ X.N * X.ccl := mul_nonneg hN0 hccl0
  have hnc : 0 ≤ (X.n' : ℝ) * X.ccl := mul_nonneg (Nat.cast_nonneg _) hccl0
  have hF8 : 8 ≤ X.cs + X.N * X.ccl + X.n' * X.ccl := by linarith
  have hprod : 1 ≤ Cb * X.k ^ 3 * X.N * X.Q ^ 4 * (X.cs + X.N * X.ccl + X.n' * X.ccl) * X.Y :=
    om _ _ (om _ _ (om _ _ (om _ _ (om _ _ (by linarith) (one_le_pow₀ (by linarith))) (by linarith))
      (one_le_pow₀ hQ1)) (by linarith)) hY1
  have hb1 : 1 ≤ X.b' := le_trans hprod hCb
  have ha5 : (5 : ℝ) ≤ X.a := by
    have h := hpab
    rw [lt_div_iff₀ hb] at h
    have := mul_le_mul hp5R hb1 (by norm_num) (by linarith)
    linarith

  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hl4 : Real.log ((2 : ℝ) ^ 2) = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hla : Real.log ((2 : ℝ) ^ 2) ≤ Real.log X.a := Real.log_le_log (by norm_num)
    (by rw [show (2 : ℝ) ^ 2 = 4 by norm_num]; linarith)
  have hloga : 1 ≤ Real.log X.a := by linarith

  have hLadef : X.La C0 = C0 * (X.N1 : ℝ) ^ 2 * Real.log X.a := rfl
  have hLa1 : 1 ≤ X.La C0 := by rw [hLadef]; exact om _ _ (om _ _ hC0 (one_le_pow₀ hN1R)) hloga
  have hLa0 : 0 ≤ X.La C0 := by linarith

  have h16 := hab16
  rw [le_div_iff₀ hb] at h16
  have hm1 : 1 ≤ X.Y * X.Yb * X.N * Real.log X.a := om _ _ (om _ _ (om _ _ hY1 hYb1) (by linarith)) hloga
  have hP1 : 1 ≤ X.Y ^ 2 * X.Yb * X.N * X.La C0 * Real.log X.a :=
    om _ _ (om _ _ (om _ _ (om _ _ hY2 hYb1) (by linarith)) hLa1) hloga
  have hkb : X.k * X.b' ≤ X.a := by
    have := mul_le_mul_of_nonneg_left hP1 (mul_nonneg hk0.le hb.le)
    linarith
  have hYLa : 0 ≤ X.Y * X.La C0 := mul_nonneg hY0 hLa0
  have hK1 : X.Y * X.La C0 * 1 ≤ X.Y * X.La C0 * (X.Y * X.Yb * X.N * Real.log X.a) :=
    mul_le_mul_of_nonneg_left hm1 hYLa
  have hK2 : 2 * (X.Y * X.La C0 * X.b') ≤ X.k * (X.Y * X.La C0 * X.b') :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hYLa hb.le)
  have hK3 : X.k * (X.Y * X.La C0 * 1) * X.b' ≤
      X.k * (X.Y * X.La C0 * (X.Y * X.Yb * X.N * Real.log X.a)) * X.b' :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK1 hk0.le) hb.le
  have hKA : 2 * X.Y * X.La C0 * X.b' ≤ X.a := by linarith

  have hLaN : 2 * X.N * X.La C0 ≤ X.k := by
    have := mul_le_mul_of_nonneg_right hYb1 (mul_nonneg hN0 hLa0)
    linarith
  have hv0 : 0 ≤ (X.N1 : ℝ) * X.La C0 / X.k := div_nonneg (mul_nonneg (by linarith) hLa0) hk0.le
  have hr0 : 0 ≤ (X.bh - X.bl) / X.b' := div_nonneg (by linarith) hb.le
  have ed : X.de C0 Cde = Cde * ((X.N1 : ℝ) * X.La C0 / X.k) + 2 * ((X.bh - X.bl) / X.b') := by
    unfold Loc.de; ring
  have hCv : 1000 * ((X.N1 : ℝ) * X.La C0 / X.k) ≤ Cde * ((X.N1 : ℝ) * X.La C0 / X.k) :=
    mul_le_mul_of_nonneg_right (by linarith) hv0
  have e40 : 40 * (X.N1 : ℝ) * X.La C0 / X.k = 40 * ((X.N1 : ℝ) * X.La C0 / X.k) := by ring
  have e18 : 18 * (X.N1 : ℝ) * X.La C0 / X.k = 18 * ((X.N1 : ℝ) * X.La C0 / X.k) := by ring
  have hLaK : 40 * (X.N1 : ℝ) * X.La C0 / X.k ≤ X.de C0 Cde := by linarith
  have eb : be X C0 = (X.bh - X.bl) / X.b' + 2 * (X.La C0 / X.k) := by unfold be; ring
  have hu0 : 0 ≤ X.La C0 / X.k := div_nonneg hLa0 hk0.le
  have hu : X.La C0 / X.k * 1 ≤ X.La C0 / X.k * X.N1 := mul_le_mul_of_nonneg_left hN1R hu0
  have eu : X.La C0 / X.k * X.N1 = (X.N1 : ℝ) * X.La C0 / X.k := by ring
  have hbeLe : be X C0 ≤ X.de C0 Cde / 2 - 18 * X.N1 * X.La C0 / X.k := by linarith
  have hbe0 : 0 ≤ be X C0 := by linarith
  have hkY : 0 < X.k * X.Y := mul_pos hk0 (by linarith)
  have eJ0 : X.J0 C0 = X.La C0 * X.b' / X.k := rfl
  have hJ0 : 0 ≤ X.J0 C0 := by rw [eJ0]; exact div_nonneg (mul_nonneg hLa0 hb.le) hk0.le
  have hJ : 2 * X.J0 C0 ≤ X.a / (X.k * X.Y) := by
    rw [le_div_iff₀ hkY]
    have eJ : 2 * X.J0 C0 * (X.k * X.Y) = 2 * X.Y * X.La C0 * X.b' := by
      rw [eJ0]; field_simp; try ring
    linarith
  have hwinA : ∀ s ∈ X.TT, (X.a : ℝ) ≤ X.aT s ∧ (X.aT s : ℝ) ≤ X.a * (1 + 2 / (X.k * X.Y)) := by
    intro s hs
    obtain ⟨h1s, h2s⟩ := hwA s hs
    refine ⟨h1s, ?_⟩
    have e : (X.a : ℝ) * (1 + 2 / (X.k * X.Y)) = X.a + X.a / (X.k * X.Y) + X.a / (X.k * X.Y) := by ring
    linarith
  have eB1 : X.b' * (1 + be X C0) = X.b' + (X.bh - X.bl) + 2 * X.J0 C0 := by
    rw [eb, eJ0]; field_simp; try ring
  have eB2 : X.b' * (1 - be X C0) = X.b' - (X.bh - X.bl) - 2 * X.J0 C0 := by
    rw [eb, eJ0]; field_simp; try ring
  have hwinB : ∀ s ∈ X.TT, X.b' * (1 - be X C0) ≤ X.bT s ∧ (X.bT s : ℝ) ≤ X.b' * (1 + be X C0) := by
    intro s hs
    obtain ⟨h1s, h2s⟩ := hwB s hs
    constructor <;> linarith
  have hab : X.k * X.Y ^ 2 * X.N * X.La C0 * Real.log X.a ≤ X.a / X.b' := by
    have hq0 : 0 ≤ X.k * X.Y ^ 2 * X.N * X.La C0 * Real.log X.a :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hk0.le (sq_nonneg _)) hN0) hLa0) (by linarith)
    have := mul_le_mul_of_nonneg_left hYb1 hq0
    linarith

  have hk2 : 1 ≤ X.k ^ 2 := by nlinarith
  have hkk3 : X.k * 1 ≤ X.k * X.k ^ 2 := mul_le_mul_of_nonneg_left hk2 hk0.le
  have hz : 0 ≤ X.N * Real.logb X.p X.a := mul_nonneg hN0 hlogb
  have hL1 : X.N * Real.logb X.p X.a * X.k ≤ X.N * Real.logb X.p X.a * (X.k * X.k ^ 2) := by
    have := mul_le_mul_of_nonneg_left hkk3 hz
    linarith
  have hs0 : 0 ≤ (X.N1 : ℝ) ^ 5 + X.k ^ 3 := add_nonneg (pow_nonneg (Nat.cast_nonneg _) 5) (pow_nonneg hk0.le 3)
  have hL2 : X.N * Real.logb X.p X.a * X.k ^ 3 ≤ X.N * Real.logb X.p X.a * ((X.N1 : ℝ) ^ 5 + X.k ^ 3) :=
    mul_le_mul_of_nonneg_left (by have := pow_nonneg (Nat.cast_nonneg X.N1 : (0 : ℝ) ≤ X.N1) 5; linarith) hz
  have hCY : 1 ≤ CD * X.Y ^ 2 := om _ _ (by linarith) hY2
  have hL3 : X.N * Real.logb X.p X.a * ((X.N1 : ℝ) ^ 5 + X.k ^ 3) * 1 ≤
      X.N * Real.logb X.p X.a * ((X.N1 : ℝ) ^ 5 + X.k ^ 3) * (CD * X.Y ^ 2) :=
    mul_le_mul_of_nonneg_left hCY (mul_nonneg hz hs0)
  have hNkL : X.N * X.k * Real.logb X.p X.a ≤ X.DLP := by linarith
  have hF0 : 0 ≤ X.cs + X.N * X.ccl + X.n' * X.ccl := by linarith
  have hcF : (X.c : ℝ) ≤ Cc * (2 * (X.cs + X.N * X.ccl + X.n' * X.ccl)) :=
    le_trans hc (mul_le_mul_of_nonneg_left (by linarith) hCc)
  have hHc' : H * X.c ≤ Cb * (X.cs + X.N * X.ccl + X.n' * X.ccl) := by
    have ha' := mul_le_mul_of_nonneg_left hcF (by linarith : (0 : ℝ) ≤ H)
    have h2CH : 2 * Cc * H ≤ Cb := le_trans hT3 t5
    have hb' := mul_le_mul_of_nonneg_right h2CH hF0
    linarith
  have hG : 0 ≤ X.k ^ 3 * X.N * X.Q ^ 4 * X.Y :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hk0.le 3) hN0) (pow_nonneg hQ0 4)) hY0
  have hHcF : H * X.k ^ 3 * X.N * X.Q ^ 4 * X.c * X.Y ≤ X.b' := by
    have := mul_le_mul_of_nonneg_left hHc' hG
    linarith
  have hHbF : H * X.k ^ 3 * X.N * X.Q ^ 4 * X.Y ≤ X.b' := by
    have hHCb : H ≤ Cb := le_trans hT4 t5
    have hHF : H * 1 ≤ Cb * (X.cs + X.N * X.ccl + X.n' * X.ccl) :=
      mul_le_mul hHCb (by linarith) zero_le_one (by linarith)
    have := mul_le_mul_of_nonneg_left hHF hG
    linarith
  have hCE1 : (0 : ℝ) ≤ CE1 := by linarith
  have hCE2 : (0 : ℝ) ≤ CE2 := by linarith
  have hE0 : 0 ≤ X.E0 C0 CE1 CE2 := by
    unfold Loc.E0 errorTermBound
    refine add_nonneg (mul_nonneg hCE1 (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_)) ?_
    · exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    · exact div_nonneg hb.le (Nat.cast_nonneg _)
    · exact div_nonneg (mul_nonneg (mul_nonneg hLa0 (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) hk0.le)
    · exact div_nonneg (mul_nonneg hLa0 hb.le) hk0.le
    · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCE2 (sq_nonneg _)) (Nat.cast_nonneg _))
        (sq_nonneg _)) (Nat.cast_nonneg _)

  have hp' : X.k ^ 2 ≤ (X.p : ℝ) := by
    have := mul_le_mul_of_nonneg_left hY2 (sq_nonneg X.k)
    linarith
  have hQ2 : 1 ≤ X.Q ^ 2 := one_le_pow₀ hQ1
  have hHc3 : X.k ^ 3 * X.Q ^ 2 * X.c ≤ X.b' := by
    have hf : 1 ≤ H * X.N * X.Q ^ 2 * X.Y := om _ _ (om _ _ (om _ _ hH (by linarith)) hQ2) hY1
    have hg : 0 ≤ X.k ^ 3 * X.Q ^ 2 * (X.c : ℝ) :=
      mul_nonneg (mul_nonneg (pow_nonneg hk0.le 3) (sq_nonneg _)) (Nat.cast_nonneg _)
    have := mul_le_mul_of_nonneg_left hf hg
    linarith
  have hHb3 : X.k ^ 3 * X.Q ≤ X.b' := by
    have hf : 1 ≤ H * X.N * X.Q ^ 3 * X.Y := om _ _ (om _ _ (om _ _ hH (by linarith)) (one_le_pow₀ hQ1)) hY1
    have hg : 0 ≤ X.k ^ 3 * X.Q := mul_nonneg (pow_nonneg hk0.le 3) hQ0
    have := mul_le_mul_of_nonneg_left hf hg
    linarith
  have hk2' : 4 * CE1 + CE2 + 1 ≤ X.k := by
    have hNL : 1 ≤ X.N * X.La C0 ^ 2 := om _ _ (by linarith) (one_le_pow₀ hLa1)
    have := mul_le_mul (le_trans hT2 t3) hNL zero_le_one (by linarith)
    linarith
  have hk1 : (1 : ℝ) ≤ X.k := by linarith
  have hc0 : (0 : ℝ) ≤ (X.c : ℝ) := Nat.cast_nonneg _
  have hN5 := error_ratio_le_epsilon hk1 hp' hN1R hLa1 hQ1 hc0 hb hkb hHc3 hHb3 hCE1 hCE2 hk2'
  exact ⟨hpP, hp5, hn2, hnEv, hY1, hpk, sq_level_le_degree, hN1, hseg, hN2, hsegB, hb, hloga, hLa1, hLaNY, hLaN,
    hLaK, hde, hbeLe, hbe0, hwinA, hwinB, hpab, hab, hband, hHcF, hHbF, hE0, hN5⟩

namespace Std

variable {C0 Cde CE1 CE2 H : ℝ} {X : Loc}

theorem one_le_level_alt (S : Std C0 Cde CE1 CE2 H X) : (1 : ℝ) ≤ X.N1 := by
  exact_mod_cast S.N1pos

theorem k5 (S : Std C0 Cde CE1 CE2 H X) : 5 ≤ X.k := by
  have h := S.N1k
  have h' := one_le_level_alt S
  linarith

theorem p5r (S : Std C0 Cde CE1 CE2 H X) : (5 : ℝ) ≤ X.p := by
  exact_mod_cast S.p5

theorem Q1 (S : Std C0 Cde CE1 CE2 H X) : 1 ≤ X.Q := by
  show (1 : ℝ) ≤ (X.p : ℝ) ^ X.G'
  exact one_le_pow₀ (by have := p5r S; linarith)

theorem apos (S : Std C0 Cde CE1 CE2 H X) : (0 : ℝ) < X.a := by
  have hne : (X.a : ℝ) ≠ 0 := by
    intro h
    have hp := S.pab
    rw [h, zero_div] at hp
    have := p5r S
    linarith
  exact lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hne)

theorem LaLeK (S : Std C0 Cde CE1 CE2 H X) : X.La C0 ≤ X.k := by
  have hL := S.LaN
  have hN := S.N2
  have hLa := S.La1
  have h : 2 * X.La C0 ≤ X.N * X.La C0 := mul_le_mul_of_nonneg_right hN (by linarith)
  nlinarith

theorem kYLab (S : Std C0 Cde CE1 CE2 H X) : X.k * X.Y * X.La C0 * X.b' ≤ X.a := by
  have hk0 : 0 ≤ X.k := by have := k5 S; linarith
  have hY := S.Y1
  have hLa := S.La1
  have hN := S.N2
  have hlog := S.loga
  have hYN : 1 ≤ X.Y * X.N := by nlinarith
  have hv : 1 * 1 ≤ X.Y * X.N * Real.log X.a := mul_le_mul hYN hlog zero_le_one (by linarith)
  have hu : 0 ≤ X.k * X.Y * X.La C0 :=
    mul_nonneg (mul_nonneg hk0 (by linarith)) (by linarith)
  have h1 : X.k * X.Y * X.La C0 * (1 * 1) ≤ X.k * X.Y * X.La C0 * (X.Y * X.N * Real.log X.a) :=
    mul_le_mul_of_nonneg_left hv hu
  have h2 : X.k * X.Y * X.La C0 ≤ X.a / X.b' := by
    have := S.ab
    nlinarith
  rw [le_div_iff₀ S.bpos] at h2
  exact h2

theorem kb (S : Std C0 Cde CE1 CE2 H X) : X.k * X.b' ≤ X.a := by
  have h := kYLab S
  have hk0 : 0 ≤ X.k := by have := k5 S; linarith
  have hY := S.Y1
  have hLa := S.La1
  have hYL : 1 ≤ X.Y * X.La C0 := by nlinarith
  have hkb : 0 ≤ X.k * X.b' := mul_nonneg hk0 S.bpos.le
  have h' : X.k * X.b' * 1 ≤ X.k * X.b' * (X.Y * X.La C0) := mul_le_mul_of_nonneg_left hYL hkb
  nlinarith

theorem ba (S : Std C0 Cde CE1 CE2 H X) : X.b' ≤ X.a := by
  have h := kb S
  have hk : (1 : ℝ) ≤ X.k := by have := k5 S; linarith
  have h' : 1 * X.b' ≤ X.k * X.b' := mul_le_mul_of_nonneg_right hk S.bpos.le
  linarith

theorem Hc2 (S : Std C0 Cde CE1 CE2 H X) (hH : 0 ≤ H) : H * (X.k ^ 3 * X.Q ^ 2 * X.c * X.Y) ≤ X.b' := by
  have hS := S.Hc
  have hQ := Q1 S
  have hN := S.N2
  have hk0 : 0 ≤ X.k := by have := k5 S; linarith
  have hY0 : 0 ≤ X.Y := by have := S.Y1; linarith
  have hQ2 : 1 ≤ X.Q ^ 2 := by nlinarith
  have hNQ : 1 ≤ X.N * X.Q ^ 2 := by nlinarith
  have hw : 0 ≤ H * X.k ^ 3 * X.Q ^ 2 * (X.c : ℝ) * X.Y :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hH (pow_nonneg hk0 3)) (pow_nonneg (by linarith) 2))
      (Nat.cast_nonneg _)) hY0
  have h' := mul_le_mul_of_nonneg_left hNQ hw
  nlinarith

theorem Hb1 (S : Std C0 Cde CE1 CE2 H X) (hH : 0 ≤ H) : H * (X.k ^ 3 * X.Q * X.Y) ≤ X.b' := by
  have hS := S.Hb
  have hQ := Q1 S
  have hN := S.N2
  have hk0 : 0 ≤ X.k := by have := k5 S; linarith
  have hY0 : 0 ≤ X.Y := by have := S.Y1; linarith
  have hQ3 : 1 ≤ X.Q ^ 3 := one_le_pow₀ hQ
  have hNQ : 1 ≤ X.N * X.Q ^ 3 := by nlinarith
  have hw : 0 ≤ H * X.k ^ 3 * X.Q * X.Y :=
    mul_nonneg (mul_nonneg (mul_nonneg hH (pow_nonneg hk0 3)) (by linarith)) hY0
  have h' := mul_le_mul_of_nonneg_left hNQ hw
  nlinarith

end Std

end Formalism.MainNotions.ColumnSystems.Pf
