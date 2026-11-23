import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.OldestFar

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

namespace Ar

theorem arith1 (dw a Bo Yk Pg PL PD sl : ℝ) (hPg : 0 < Pg) (hPL : 0 < PL) (hYk : 0 < Yk) (hBo : 0 ≤ Bo)
    (ha : 0 ≤ a) (h1 : dw ≤ 3 * a / Pg) (h2 : a ≤ Bo * PD) (h3 : PD * PL ≤ Pg) (h4 : 48 * Yk ≤ PL)
    (h5 : Bo / Yk ≤ 2 * sl) : dw ≤ 1 / 8 * sl := by
  have e1 : a / Pg ≤ Bo / PL := by
    rw [div_le_div_iff₀ hPg hPL]
    nlinarith [mul_le_mul_of_nonneg_left h3 hBo, mul_le_mul_of_nonneg_right h2 hPL.le]
  have e2 : Bo / PL ≤ Bo / (48 * Yk) := div_le_div_of_nonneg_left hBo (by positivity) h4
  have e3 : Bo / (48 * Yk) = (Bo / Yk) / 48 := by
    field_simp
  have e4 : 3 * a / Pg = 3 * (a / Pg) := by ring
  linarith

theorem size_le_monomial_product (C k r N Q cS e Y : ℝ) (hC : 1 ≤ C) (hk : 1 ≤ k) (hr : 1 ≤ r) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hcS : 1 ≤ cS) (he : 0 ≤ e) (hY : 0 ≤ Y) : Y * k ^ 2 * Q ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 * (cS + e) * Y := by
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have hQ4 : 1 ≤ Q ^ 4 := one_le_pow₀ hQ
  have hce : 1 ≤ cS + e := by linarith
  have hf : 1 ≤ C * k * r ^ 2 * N * Q ^ 4 * (cS + e) := by
    calc (1 : ℝ) = 1 * 1 * 1 * 1 * 1 * 1 := by norm_num
      _ ≤ C * k * r ^ 2 * N * Q ^ 4 * (cS + e) := by gcongr
  have h0 : 0 ≤ Y * k ^ 2 * Q := by positivity
  calc Y * k ^ 2 * Q = Y * k ^ 2 * Q * 1 := by ring
    _ ≤ Y * k ^ 2 * Q * (C * k * r ^ 2 * N * Q ^ 4 * (cS + e)) := mul_le_mul_of_nonneg_left hf h0
    _ = _ := by ring

theorem forty_eight_bound_arith (Y k N P : ℝ) (hY : 2 ≤ Y) (hk : 1 ≤ k) (hN : 1 ≤ N) (h : 256 * k ^ 2 * N * Y ^ 2 ≤ P) :
    48 * (Y * k ^ 2) ≤ P := by
  have h1 : 256 * k ^ 2 * Y ^ 2 ≤ 256 * k ^ 2 * N * Y ^ 2 := by
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 256 * k ^ 2 * Y ^ 2) (by linarith : (0:ℝ) ≤ N - 1)]
  have h2 : 48 * (Y * k ^ 2) ≤ 256 * k ^ 2 * Y ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg k) (by linarith : (0:ℝ) ≤ Y)) (by linarith : (0:ℝ) ≤ 256 * Y - 48)]
  linarith

end Ar

set_option maxHeartbeats 1000000 in

theorem arithCondition_of_one_le (C CLa : ℝ) (hC : 1 ≤ C) : RestArithStep C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K _ _ hk
    F nb B hD
  obtain ⟨_, H, hF, _⟩ := hD
  have hB := hyps_basic hC H
  obtain ⟨h1, h2, h3, h4, h5, h6, _, _, h9, _, h11, h12⟩ := H
  obtain ⟨hTT, hV, hG, _⟩ := hF
  have hr1 : 1 ≤ r := by omega
  have ha0 : (0 : ℝ) ≤ a := by linarith [hB.two_le_a]
  refine ⟨?_, ?_⟩
  · by_contra hc
    have hJ1 : F.J = 1 := by have := hV.1; omega
    have e := hV.2.1 0 (r - 1)
    rw [hJ1] at e
    simp only [Nat.cast_one, zero_add] at e
    have g := hG 1
    simp only [sub_self] at g
    have m0 := frame_row_monotone F L₁ _ hV 0 (r - 1) (by omega)
    have h3G := h3.2.2.2
    omega
  intro E' l hl ga hga J _ Dt hS dPl dNo rho hb hlow jj mm hmm
  obtain ⟨t1, t2, _, t5, _, _⟩ := hS
  obtain ⟨s, hs⟩ := seg_shift hV t1 (jj - 1)
  rw [sub_add_cancel jj 1] at hs
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
  set q : ℝ := (p : ℝ)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq13 : q ≤ 1 / 3 := by
    rw [hq, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hp3
  have hq1 : q < 1 := by linarith
  set g : ℕ := (F.fr (segZ jj) (r - 1) - F.fr (segZ jj - 1) (r - 1)).toNat with hg
  let t : Fin r → ℕ := fun m' => (F.fr (segZ jj - 1) (r - 1) - F.fr (segZ jj - 1) (r - 1 - m'.val)).toNat
  have ht : Function.Injective t := by
    intro u v huv
    have huv' : (F.fr (segZ jj - 1) (r - 1) - F.fr (segZ jj - 1) (r - 1 - u.val)).toNat =
        (F.fr (segZ jj - 1) (r - 1) - F.fr (segZ jj - 1) (r - 1 - v.val)).toNat := huv
    have l1 := frame_entry_le_last F L₁ _ hV (segZ jj - 1) (r - 1 - u.val) (by omega)
    have l2 := frame_entry_le_last F L₁ _ hV (segZ jj - 1) (r - 1 - v.val) (by omega)
    have hu := u.isLt
    have hv := v.isLt
    apply Fin.ext
    rcases lt_trichotomy u.val v.val with c | c | c
    · have := frame_entries_strictMono F L₁ _ hV (segZ jj - 1) (r - 1 - v.val) (r - 1 - u.val) (by omega) (by omega)
      omega
    · exact c
    · have := frame_entries_strictMono F L₁ _ hV (segZ jj - 1) (r - 1 - u.val) (r - 1 - v.val) (by omega) (by omega)
      omega

  have hterm : ∀ m' : Fin r, ((dPl ⟨jj - 1, Sum.inr m'⟩ -
      multideg (plMon F p hk Dt.nL (l.mapDomain (castV hk) + ga)) ⟨jj - 1, Sum.inr m'⟩ : ℕ) : ℝ) /
        (Dt.P (jj - 1) m' : ℝ) ≤ 2 * a * q ^ g * q ^ t m' := by
    intro m'
    have hd := Ar.deg_le F p hk Dt.nL hV hr1 t2 (G2d F (flatDeg lam0) E') l hl ga hga dPl dNo rho hb hlow
      ⟨jj - 1, Sum.inr m'⟩
    have htop := (posTL_seg F hV hr1 t2 (⟨jj - 1, Sum.inr m'⟩ : TL J Dt.nL r)).2.2
    have hG2 : G2d F (flatDeg lam0) E' (posOf n' (posTL F (⟨jj - 1, Sum.inr m'⟩ : TL J Dt.nL r))) ≤
        flatDeg lam0 (posOf n' (posTL F (⟨jj - 1, Sum.inr m'⟩ : TL J Dt.nL r))) := by
      unfold G2d
      rw [if_pos htop]
      exact Nat.sub_le _ _
    have hfd := (flatDeg_bounds (by have := hB.m_ge; omega) ha0 h5 _ (hTT ▸ htop)).2
    have s1 := hs (r - 1)
    have s2 := hs (r - 1 - m'.val)
    have hlowP : lowP F p (⟨jj - 1, Sum.inr m'⟩ : TL J Dt.nL r) = p ^ t m' := by
      show p ^ (F.fr (segZ (jj - 1)) (r - 1) - F.fr (segZ (jj - 1)) (r - 1 - m'.val)).toNat =
        p ^ (F.fr (segZ jj - 1) (r - 1) - F.fr (segZ jj - 1) (r - 1 - m'.val)).toNat
      congr 1
      omega
    have hP : Dt.P (jj - 1) m' = p ^ g := by
      unfold SignedChainData.P
      rw [t5, hg]
      congr 1
      omega
    rw [hlowP] at hd
    set nn : ℕ := dPl ⟨jj - 1, Sum.inr m'⟩ -
      multideg (plMon F p hk Dt.nL (l.mapDomain (castV hk) + ga)) ⟨jj - 1, Sum.inr m'⟩ with hnn
    have h3' : ((p ^ t m' * nn : ℕ) : ℝ) ≤ 2 * a := le_trans (by exact_mod_cast le_trans hd hG2) hfd
    push_cast at h3'
    have hpt : (0 : ℝ) < (p : ℝ) ^ t m' := by positivity
    have hn : (nn : ℝ) ≤ 2 * a * q ^ t m' := by
      rw [hq, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpt]
      linarith
    rw [hP]
    push_cast
    calc (nn : ℝ) / (p : ℝ) ^ g = nn * q ^ g := by rw [hq, inv_pow, div_eq_mul_inv]
      _ ≤ 2 * a * q ^ t m' * q ^ g := mul_le_mul_of_nonneg_right hn (by positivity)
      _ = 2 * a * q ^ g * q ^ t m' := by ring
  have hinv : (1 - q)⁻¹ ≤ 3 / 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hA : 0 ≤ 2 * a * q ^ g := by positivity
  have hsum : dwB F hk Dt dPl (l.mapDomain (castV hk) + ga) jj ≤ 3 * a / (p : ℝ) ^ g := by
    unfold dwB
    calc _ ≤ ∑ m' : Fin r, 2 * a * q ^ g * q ^ t m' := Finset.sum_le_sum fun m' _ => hterm m'
      _ = 2 * a * q ^ g * ∑ m' : Fin r, q ^ t m' := by rw [Finset.mul_sum]
      _ ≤ 2 * a * q ^ g * (1 - q)⁻¹ := mul_le_mul_of_nonneg_left (geom_inj_le t ht q hq0 hq1) hA
      _ ≤ 2 * a * q ^ g * (3 / 2) := mul_le_mul_of_nonneg_left hinv hA
      _ = 3 * a / (p : ℝ) ^ g := by rw [hq, inv_pow, div_eq_mul_inv]; ring

  have hi0 : r - 1 - mm.val < r := by omega
  have ex0 : posU F (Dt.nL jj) (segZ jj) (Dt.nL jj + (r - 1 - mm.val)) = F.fr (segZ jj) (r - 1 - mm.val) :=
    posU_fr' (Fr := F) _ _ _
  unfold slU
  rw [ex0]
  have hx := posU_mem' hV hr1 (segZ jj) ((F.LLset (segZ jj)).card + (r - 1 - mm.val)) (by omega)
  rw [posU_fr] at hx
  have hfar := Ar.oldest_far hV hr1 (segZ jj) (r - 1 - mm.val) hi0
  have hy := oldest_mem_segment_letters F L₁ _ hV hr1 (segZ jj) _ hx.1 hx.2
  unfold Frames.letters at hy
  simp only [Finset.mem_filter, Finset.mem_Icc] at hy
  set y : ℤ := F.oldest (segZ jj) (F.fr (segZ jj) (r - 1 - mm.val)) with hydef
  set Dd : ℕ := F.dist (segZ jj) y with hDd
  have hDd' : Dd = (F.fr (segZ jj) (r - 1) - y).toNat := rfl
  have hdeg := (flatDeg_bounds (by have := hB.m_ge; omega) ha0 h5 _ (hTT ▸ hy.2)).1
  have hPD : (0 : ℝ) < (p : ℝ) ^ Dd := by positivity
  have hBoe : Bo p F (flatDeg lam0) (segZ jj) (F.fr (segZ jj) (r - 1 - mm.val)) =
      (flatDeg lam0 (posOf n' y) : ℝ) / (p : ℝ) ^ Dd := rfl
  set Bv : ℝ := Bo p F (flatDeg lam0) (segZ jj) (F.fr (segZ jj) (r - 1 - mm.val)) with hBv
  have hBo0 : 0 ≤ Bv := by rw [hBoe]; positivity
  have hBoa : a ≤ Bv * (p : ℝ) ^ Dd := by rw [hBoe, div_mul_cancel₀ _ hPD.ne']; exact hdeg
  have hpow : (p : ℝ) ^ Dd * (p : ℝ) ^ (L₁ + 1) ≤ (p : ℝ) ^ g := by
    rw [← pow_add]
    apply pow_le_pow_right₀ hp1
    omega
  have hkk : ((r + K : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) := by rw [hk]
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hNN : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hB.N_pos
  have hY2 := hB.two_le_Y
  have hY0 : (0 : ℝ) < Y := by linarith
  have hden : 0 < Y * ((r + K : ℕ) : ℝ) ^ 2 := by rw [hkk]; positivity
  have hQ1 : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := one_le_pow₀ hp1
  have hQ0 : (0 : ℝ) < (p : ℝ) ^ goodG' r de h x := by linarith
  have hcS : (1 : ℝ) ≤ (cStar : ℝ) := by exact_mod_cast (by omega : 1 ≤ cStar)
  have hsz := le_trans (Ar.size_le_monomial_product C ((m + 1 : ℕ) : ℝ) r TT.card ((p : ℝ) ^ goodG' r de h x) cStar
    ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp) Y hC hk1 hrr hNN hQ1 hcS (by positivity) hY0.le) h12
  have hDG : Dd ≤ goodG' r de h x := by
    have g1 := hG (segZ jj)
    have g2 := frame_row_monotone F L₁ _ hV (segZ jj - 1) (r - 1) (by omega)
    omega
  have hX1 : (1 : ℝ) ≤ Bv / (Y * ((r + K : ℕ) : ℝ) ^ 2) := by
    rw [le_div_iff₀ hden, one_mul, hkk]
    have c1 : (p : ℝ) ^ Dd ≤ (p : ℝ) ^ goodG' r de h x := pow_le_pow_right₀ hp1 hDG
    have c2 : Bv * (p : ℝ) ^ Dd ≤ Bv * (p : ℝ) ^ goodG' r de h x := mul_le_mul_of_nonneg_left c1 hBo0
    exact le_of_mul_le_mul_right (by linarith) hQ0
  have f1 : (1 : ℤ) ≤ sl p F (flatDeg lam0) Y (r + K) (segZ jj) (F.fr (segZ jj) (r - 1 - mm.val)) := by
    unfold sl
    exact Int.le_floor.2 (by rw [Int.cast_one]; exact hX1)
  have f2 : Bv / (Y * ((r + K : ℕ) : ℝ) ^ 2) <
      (sl p F (flatDeg lam0) Y (r + K) (segZ jj) (F.fr (segZ jj) (r - 1 - mm.val)) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have f1' : (1 : ℝ) ≤ (sl p F (flatDeg lam0) Y (r + K) (segZ jj) (F.fr (segZ jj) (r - 1 - mm.val)) : ℝ) := by
    exact_mod_cast f1
  have h48 : 48 * (Y * ((r + K : ℕ) : ℝ) ^ 2) ≤ (p : ℝ) ^ (L₁ + 1) := by
    rw [hkk]
    have z1 : (p : ℝ) ^ ((L₁ : ℤ) - 1) ≤ (p : ℝ) ^ ((L₁ + 1 : ℕ) : ℤ) :=
      zpow_le_zpow_right₀ hp1 (by push_cast; omega)
    rw [zpow_natCast] at z1
    exact Ar.forty_eight_bound_arith Y _ _ _ hY2 hk1 hNN (le_trans h9 z1)
  exact Ar.arith1 _ a Bv _ ((p : ℝ) ^ g) ((p : ℝ) ^ (L₁ + 1)) ((p : ℝ) ^ Dd) _ (by positivity) (by positivity) hden hBo0
    ha0 hsum hBoa hpow h48 (by linarith)

theorem restArith_all : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ, RestArithStep C CLa := ⟨1, one_pos, fun C hC CLa => arithCondition_of_one_le C CLa hC⟩

end Formalism.MainNotions.PairMembershipBlocks
