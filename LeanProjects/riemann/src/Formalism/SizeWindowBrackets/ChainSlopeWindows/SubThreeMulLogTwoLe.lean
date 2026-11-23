import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse

open Real

namespace Formalism.LFunctionChainParameters.LErr

open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds

set_option linter.unusedVariables false

set_option maxHeartbeats 1000000 in

theorem core_ineq {nT a b b' k L La B0 Nc M sA lW lk lH dI et Xpp y yD yL K h g
    cDiv cE cH cCount cSlope cSl1 cLoss : ℝ}
    (hy : 1 ≤ y) (hyD : 1 ≤ yD) (hyL : 1 ≤ yL)
    (hnT : 1 ≤ nT) (ha1 : 1 ≤ a) (hb0 : 0 ≤ b) (hba : b ≤ a) (hM : 0 ≤ M) (hk : 0 < k) (hMk : M ≤ k)
    (hMb : M * b ≤ a) (hL0 : 0 ≤ L) (hL : L ≤ 2 * y) (hLa0 : 0 ≤ La) (hLa : La ≤ 2 * y)
    (hb' : 0 ≤ b') (hkb' : k * b' ≤ a) (hX0 : 0 ≤ Xpp) (hX : Xpp ≤ a)
    (hsA0 : 0 ≤ sA) (hsA : sA ≤ 2 * (nT * a)) (hB0 : 0 ≤ B0) (hNc : 0 ≤ Nc)
    (hlW : lW ≤ a) (hlk0 : 0 ≤ lk) (hlk : lk ≤ g * y) (hlH0 : 0 ≤ lH) (hlH : lH ≤ h * y)
    (hdI0 : 0 ≤ dI) (hdI : dI ≤ 2) (het : et ≤ K * y * (nT * a))
    (c1 : 0 ≤ cDiv) (c1' : cDiv ≤ K) (c2 : 0 ≤ cE) (c2' : cE ≤ K) (c3 : 0 ≤ cH) (c3' : cH ≤ K)
    (c4 : 0 ≤ cCount) (c4' : cCount ≤ K) (c5 : 0 ≤ cSlope) (c5' : cSlope ≤ K)
    (c6 : 0 ≤ cSl1) (c6' : cSl1 ≤ K) (c7 : 0 ≤ cLoss) (c7' : cLoss ≤ K)
    (hh : 1 ≤ h) (hg : 1 ≤ g) (hbig : 200 * (1 + K) ^ 2 * h * g ≤ y) :
    sA * (cCount * (La + M ^ 2 * La / k))
      + (cDiv * nT * a * La + cDiv * M * (B0 + Nc) * yD)
      + M * cE * B0
      + cSlope * nT * a * La * (1 + M / k)
      + lW
      + cLoss * nT * M * b * yL
      + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
          + cSl1 * Xpp + 1)
      + dI * (4 * lH * ((cSlope * nT * a * La * (2 + M / k)
            + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
            + cSl1 * M * B0
            + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
                + cSl1 * Xpp + 1)) + b) + et)
      ≤ yD * yL * y * y * y * (nT * a * (1 + M ^ 2 / k) + M * (B0 + Nc)) := by
  have hK : 0 ≤ K := c1.trans c1'
  have hy0 : 0 ≤ y := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hnT0 : 0 ≤ nT := by linarith
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨r, hr⟩ : ∃ r, r = M ^ 2 / k := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  obtain ⟨q, hq⟩ : ∃ q, q = M / k := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by rw [hq]; exact (div_le_one hk).2 hMk
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = nT * a := ⟨_, rfl⟩
  have hA1a : a ≤ A1 := by rw [hA1]; exact le_mul_of_one_le_left ha0 hnT
  have hA10 : 0 ≤ A1 := by linarith
  obtain ⟨A3, hA3⟩ : ∃ A3, A3 = M * B0 := ⟨_, rfl⟩
  have hA30 : 0 ≤ A3 := by rw [hA3]; positivity
  obtain ⟨A4, hA4⟩ : ∃ A4, A4 = M * Nc := ⟨_, rfl⟩
  have hA40 : 0 ≤ A4 := by rw [hA4]; positivity
  obtain ⟨E, hE⟩ : ∃ E, E = A1 * (1 + r) + (A3 + A4) := ⟨_, rfl⟩
  have hA1r : 0 ≤ A1 * r := mul_nonneg hA10 hr0
  have orbitMap_conj_smul_one : A1 ≤ E := by rw [hE]; linarith only [hA1r, hA30, hA40]
  have eA1r : A1 * (1 + r) ≤ E := by rw [hE]; linarith only [hA30, hA40]
  have orbitMap_conj_smul_two : A1 * r ≤ E := by rw [hE]; linarith only [hA10, hA30, hA40]
  have selfLieBasisVector : A3 ≤ E := by rw [hE]; linarith only [hA10, hA1r, hA40]
  have eA34 : A3 + A4 ≤ E := by rw [hE]; linarith only [hA10, hA1r]
  have hE0 : 0 ≤ E := hA10.trans orbitMap_conj_smul_one
  have e1 : 1 ≤ E := by linarith only [ha1, hA1a, orbitMap_conj_smul_one]
  obtain ⟨Y, hY⟩ : ∃ Y, Y = yD * yL * y := ⟨_, rfl⟩
  have hDL : 1 ≤ yD * yL := one_le_mul_of_one_le_of_one_le hyD hyL
  have yY : y ≤ Y := by rw [hY]; exact le_mul_of_one_le_left hy0 hDL
  have oneY : 1 ≤ Y := hy.trans yY
  have yDY : yD ≤ Y := by
    rw [hY, mul_assoc]
    exact le_mul_of_one_le_right (by linarith) (one_le_mul_of_one_le_of_one_le hyL hy)
  have yLY : yL ≤ Y := by
    have : yL ≤ yD * yL := le_mul_of_one_le_left (by linarith) hyD
    rw [hY]
    exact this.trans (le_mul_of_one_le_right (by linarith) hy)
  have hY0 : 0 ≤ Y := by linarith
  obtain ⟨P, hP⟩ : ∃ P, P = Y * E := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have EP : E ≤ P := by rw [hP]; exact le_mul_of_one_le_left hE0 oneY
  have hLaY : La ≤ 2 * Y := by linarith only [hLa, yY]
  have hLY : L ≤ 2 * Y := by linarith only [hL, yY]
  have hlkY : lk ≤ g * Y := hlk.trans (by gcongr)

  have T1 : sA * (cCount * (La + M ^ 2 * La / k)) ≤ 4 * K * P := by
    have e : sA * (cCount * (La + M ^ 2 * La / k)) = (sA * (1 + r)) * (cCount * La) := by
      rw [hr]; ring
    have s1 : sA * (1 + r) ≤ 2 * E := by
      have : sA * (1 + r) ≤ 2 * A1 * (1 + r) := by rw [hA1]; gcongr
      linarith only [this, eA1r]
    rw [e]
    calc (sA * (1 + r)) * (cCount * La) ≤ (2 * E) * (K * (2 * Y)) := by gcongr
      _ = 4 * K * P := by rw [hP]; ring
  have T2a : cDiv * nT * a * La ≤ 2 * K * P := by
    calc cDiv * nT * a * La = cDiv * A1 * La := by rw [hA1]; ring
      _ ≤ K * E * (2 * Y) := by gcongr
      _ = 2 * K * P := by rw [hP]; ring
  have T2b : cDiv * M * (B0 + Nc) * yD ≤ K * P := by
    calc cDiv * M * (B0 + Nc) * yD = cDiv * (A3 + A4) * yD := by rw [hA3, hA4]; ring
      _ ≤ K * E * Y := by gcongr
      _ = K * P := by rw [hP]; ring
  have T3 : M * cE * B0 ≤ K * P := by
    calc M * cE * B0 = cE * A3 := by rw [hA3]; ring
      _ ≤ K * P := by gcongr; exact selfLieBasisVector.trans EP
  have T4 : cSlope * nT * a * La * (1 + M / k) ≤ 4 * K * P := by
    calc cSlope * nT * a * La * (1 + M / k) = cSlope * A1 * La * (1 + q) := by rw [hA1, hq]; ring
      _ ≤ K * E * (2 * Y) * (1 + 1) := by gcongr
      _ = 4 * K * P := by rw [hP]; ring
  have T5 : lW ≤ P := by linarith only [hlW, hA1a, orbitMap_conj_smul_one, EP]
  have T60 : 0 ≤ cLoss * nT * M * b * yL := by positivity
  have FreeQuotientRank : cLoss * nT * M * b * yL ≤ K * P := by
    calc cLoss * nT * M * b * yL = cLoss * (nT * (M * b)) * yL := by ring
      _ ≤ K * (nT * a) * Y := by gcongr
      _ ≤ K * E * Y := by rw [← hA1]; gcongr
      _ = K * P := by rw [hP]; ring
  have Tmid : cSl1 * nT * M * (a / k + b') * (cCount * M * L) ≤ 4 * K ^ 2 * P := by
    have hb'k : b' ≤ a / k := by rw [le_div_iff₀ hk]; linarith
    have hQ : nT * M ^ 2 * (a / k + b') ≤ 2 * E := by
      calc nT * M ^ 2 * (a / k + b') ≤ nT * M ^ 2 * (a / k + a / k) := by gcongr
        _ = 2 * (A1 * r) := by rw [hA1, hr]; ring
        _ ≤ 2 * E := by linarith
    have hQ0 : 0 ≤ nT * M ^ 2 * (a / k + b') := by positivity
    calc cSl1 * nT * M * (a / k + b') * (cCount * M * L)
        = cSl1 * cCount * L * (nT * M ^ 2 * (a / k + b')) := by ring
      _ ≤ K * K * (2 * Y) * (2 * E) := by gcongr
      _ = 4 * K ^ 2 * P := by rw [hP]; ring
  have T7 : cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
      + cSl1 * Xpp + 1 ≤ (5 * K ^ 2 + K + 1) * P := by
    have s1 : cSl1 * (cLoss * nT * M * b * yL) ≤ K * (K * P) := by gcongr
    have s2 : cSl1 * Xpp ≤ K * P := by gcongr; linarith only [hX, hA1a, orbitMap_conj_smul_one, EP]
    have s3 : 1 ≤ P := e1.trans EP
    linarith only [s1, s2, s3, Tmid]
  have TU : cSlope * nT * a * La * (2 + M / k)
      + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
      + cSl1 * M * B0
      + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
          + cSl1 * Xpp + 1) + b ≤ (5 * K ^ 2 + 13 * K + 2 * K * g + 2) * P := by
    have s1 : cSlope * nT * a * La * (2 + M / k) ≤ 6 * K * P := by
      calc cSlope * nT * a * La * (2 + M / k) = cSlope * A1 * La * (2 + q) := by rw [hA1, hq]; ring
        _ ≤ K * E * (2 * Y) * (2 + 1) := by gcongr
        _ = 6 * K * P := by rw [hP]; ring
    have s2 : cH * (nT * a * La + M * B0) ≤ 3 * K * P := by
      calc cH * (nT * a * La + M * B0) = cH * (A1 * La + A3) := by rw [hA1, hA3]
        _ ≤ K * (E * (2 * Y) + P) := by gcongr; exact selfLieBasisVector.trans EP
        _ = 3 * K * P := by rw [hP]; ring
    have s3 : sA * (cCount * lk) ≤ 2 * K * g * P := by
      calc sA * (cCount * lk) ≤ (2 * E) * (K * (g * Y)) := by
            gcongr
            rw [← hA1] at hsA; linarith
        _ = 2 * K * g * P := by rw [hP]; ring
    have s4 : cSl1 * M * B0 ≤ K * P := by
      calc cSl1 * M * B0 = cSl1 * A3 := by rw [hA3]; ring
        _ ≤ K * P := by gcongr; exact selfLieBasisVector.trans EP
    have s5 : b ≤ P := by linarith only [hba, hA1a, orbitMap_conj_smul_one, EP]
    linarith only [s1, s2, s3, s4, s5, T3, T7]
  have Tet : et ≤ K * P := by
    calc et ≤ K * y * A1 := by rw [hA1]; exact het
      _ ≤ K * Y * E := by gcongr
      _ = K * P := by rw [hP]; ring
  obtain ⟨u, hu⟩ : ∃ u, u = 5 * K ^ 2 + 13 * K + 2 * K * g + 2 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  rw [← hu] at TU
  have T8 : dI * (4 * lH * ((cSlope * nT * a * La * (2 + M / k)
            + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
            + cSl1 * M * B0
            + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
                + cSl1 * Xpp + 1)) + b) + et) ≤ 2 * (4 * (h * y) * (u * P) + K * P) := by
    have s1 : 4 * lH * ((cSlope * nT * a * La * (2 + M / k)
            + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
            + cSl1 * M * B0
            + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
                + cSl1 * Xpp + 1)) + b) ≤ 4 * (h * y) * (u * P) := by
      calc _ ≤ 4 * lH * (u * P) := by gcongr
        _ ≤ 4 * (h * y) * (u * P) := by gcongr
    have s2 : 0 ≤ 4 * (h * y) * (u * P) + K * P := by positivity
    calc _ ≤ dI * (4 * (h * y) * (u * P) + K * P) := by gcongr
      _ ≤ 2 * (4 * (h * y) * (u * P) + K * P) := by gcongr

  have hyP : P ≤ y * P := le_mul_of_one_le_left hP0 hy
  have hyP0 : 0 ≤ y * P := by positivity
  have hsum : (5 * K ^ 2 + 16 * K + 2) + 8 * h * u ≤ 200 * (1 + K) ^ 2 * h * g := by
    rw [hu]
    have hhg : 1 ≤ h * g := one_le_mul_of_one_le_of_one_le hh hg
    have a1 : (5 * K ^ 2 + 16 * K + 2) ≤ (5 * K ^ 2 + 16 * K + 2) * (h * g) :=
      le_mul_of_one_le_right (by positivity) hhg
    have a2 : 8 * h * (5 * K ^ 2 + 13 * K + 2 * K * g + 2)
        ≤ 8 * h * ((5 * K ^ 2 + 15 * K + 2) * g) := by
      gcongr
      have := mul_nonneg (by positivity : 0 ≤ 5 * K ^ 2 + 13 * K + 2) (by linarith only [hg] : 0 ≤ g - 1)
      linarith only [this]
    have a3 : (5 * K ^ 2 + 16 * K + 2) * (h * g) + 8 * h * ((5 * K ^ 2 + 15 * K + 2) * g)
        ≤ 200 * (1 + K) ^ 2 * h * g := by
      have : 0 ≤ (155 * K ^ 2 + 264 * K + 182) * (h * g) := by positivity
      linarith only [this]
    linarith only [a1, a2, a3]
  have hfin : (5 * K ^ 2 + 14 * K + 2) * P + 2 * (4 * (h * y) * (u * P) + K * P)
      ≤ y * (y * P) := by
    have b1 : (5 * K ^ 2 + 16 * K + 2) * P ≤ (5 * K ^ 2 + 16 * K + 2) * (y * P) := by gcongr
    have b2 : ((5 * K ^ 2 + 16 * K + 2) + 8 * h * u) * (y * P) ≤ y * (y * P) := by
      gcongr
      exact hsum.trans hbig
    linarith only [b1, b2]
  have hR : yD * yL * y * y * y * (nT * a * (1 + M ^ 2 / k) + M * (B0 + Nc)) = y * (y * P) := by
    rw [hP, hY, hE, hA1, hA3, hA4, hr]; ring
  rw [hR]
  linarith only [T1, T2a, T2b, T3, T4, T5, FreeQuotientRank, T7, T8, hfin]

lemma umean_le_of_le {ι : Type} [Fintype ι] (X : ι → ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ i, X i ≤ B) :
    umean X ≤ B := by
  unfold umean
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
  · rw [h0]; simpa using hB
  · have hc : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast h0
    rw [div_le_iff₀ hc]
    calc ∑ i, X i ≤ ∑ _i : ι, B := Finset.sum_le_sum (fun i _ => h i)
      _ = B * (Fintype.card ι : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

lemma log_one_add_rpow_le {x c y : ℝ} (hx : 1 ≤ x) (hc : 0 ≤ c) (hlog : Real.log x ≤ y)
    (hy : 1 ≤ y) : Real.log (1 + x ^ c) ≤ (1 + c) * y := by
  have hx0 : 0 < x := by linarith
  have hxH : 1 ≤ x ^ c := Real.one_le_rpow hx hc
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  calc Real.log (1 + x ^ c) ≤ Real.log (2 * x ^ c) :=
        Real.log_le_log (by linarith) (by linarith)
    _ = Real.log 2 + c * Real.log x := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0]
    _ ≤ 1 * y + c * y := by
        gcongr
        linarith
    _ = (1 + c) * y := by ring

lemma log_le_of_le_rpow {x k e y : ℝ} (hx : 1 ≤ x) (he : 0 ≤ e) (hk : 0 < k) (hkx : k ≤ x ^ e)
    (hlog : Real.log x ≤ y) (hy : 1 ≤ y) : Real.log k ≤ (1 + e) * y := by
  have hx0 : 0 < x := by linarith
  calc Real.log k ≤ Real.log (x ^ e) := Real.log_le_log hk hkx
    _ = e * Real.log x := Real.log_rpow hx0 _
    _ ≤ e * y := by gcongr
    _ ≤ (1 + e) * y := by linarith

lemma sub_three_mul_log_two_le {k : ℝ} (hk : 0 ≤ k) : (k - 3) * Real.log 2 ≤ k := by
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have := mul_nonneg hk (by linarith : 0 ≤ 1 - Real.log 2)
  linarith

lemma inv_one_sub_le_two {d : ℝ} (hd : d ≤ 1 / 2) : 0 ≤ (1 - d)⁻¹ ∧ (1 - d)⁻¹ ≤ 2 := by
  have hd12 : (1 : ℝ) / 2 ≤ 1 - d := by linarith
  refine ⟨inv_nonneg.2 (by linarith), ?_⟩
  have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hd12
  simpa using this

set_option maxHeartbeats 1000000 in
theorem error_sizes : ErrorFormsUnderWindows := by
  intro U0 _ W _ _ Top _ m f D C Xpp eK K hW hX
  obtain ⟨⟨hx, hε, hε1, hb, hxb, hnT, hm, hxm, heK, hk1, hkx, hka, hL0, hL, hLa0, hLa, hb', hkb', hX0,
    hXa, haT, hB0, hNc, hlW, hdel, -, -, hC⟩, het⟩ := hW
  obtain ⟨c1, c1', c2, c2', c3, c3', c4, c4', c5, c5', c6, c6', c7, c7', hD, hLs, hHH⟩ := hC
  obtain ⟨hlog, hbig⟩ := hX
  have hx0 : 0 < D.x := by linarith only [hx]
  have hy : 1 ≤ D.x ^ D.ε := Real.one_le_rpow hx hε.le
  have hyD : 1 ≤ D.x ^ (C.eDiv * D.ε) := Real.one_le_rpow hx (mul_nonneg hD hε.le)
  have hyL : 1 ≤ D.x ^ (C.eLoss * D.ε) := Real.one_le_rpow hx (mul_nonneg hLs hε.le)
  have hb0 : 0 ≤ D.b := by linarith only [hb]
  have hbxb : D.b ≤ D.x * D.b := le_mul_of_one_le_left hb0 hx
  have hba : D.b ≤ D.a := hbxb.trans hxb
  have ha1 : 1 ≤ D.a := hb.trans hba
  have hM : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hk : 0 < D.k := by linarith only [hk1]
  have hmx : (m : ℝ) ≤ D.x := by
    refine hm.trans ?_
    calc D.x ^ ((1 : ℝ) / 2 + D.ε / 2) ≤ D.x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hε1])
      _ = D.x := Real.rpow_one _
  have hMk : (m : ℝ) ≤ D.k := (le_mul_of_one_le_left hM hx).trans hxm
  have hMb : (m : ℝ) * D.b ≤ D.a := (mul_le_mul_of_nonneg_right hmx hb0).trans hxb
  have hsA0 : 0 ≤ D.sumA := Finset.sum_nonneg (fun t _ => (haT t).1)
  have hsA : D.sumA ≤ 2 * (D.nT * D.a) := by
    unfold Data.sumA Data.nT
    calc ∑ t, D.aT t ≤ ∑ _t : Top, 2 * D.a := Finset.sum_le_sum (fun t _ => (haT t).2)
      _ = 2 * ((Fintype.card Top : ℝ) * D.a) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hlWk : umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ)) ≤ D.a :=
    (umean_le_of_le _ D.k hk.le
      (fun u0 => (hlW u0).trans (sub_three_mul_log_two_le hk.le))).trans hka
  have hlk0 : 0 ≤ Real.log D.k := Real.log_nonneg hk1
  have hlk : Real.log D.k ≤ (1 + eK) * D.x ^ D.ε := log_le_of_le_rpow hx heK hk hkx hlog hy
  have hxH : 1 ≤ D.x ^ C.cHH := Real.one_le_rpow hx hHH
  have hlH0 : 0 ≤ Real.log (1 + D.x ^ C.cHH) := Real.log_nonneg (by linarith only [hxH])
  have hlH : Real.log (1 + D.x ^ C.cHH) ≤ (1 + C.cHH) * D.x ^ D.ε :=
    log_one_add_rpow_le hx hHH hlog hy
  obtain ⟨hdI0, hdI⟩ := inv_one_sub_le_two hdel
  have hpow : D.x ^ (CErr C * D.ε)
      = D.x ^ (C.eDiv * D.ε) * D.x ^ (C.eLoss * D.ε) * D.x ^ D.ε * D.x ^ D.ε * D.x ^ D.ε := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    unfold CErr
    ring
  rw [hpow]
  unfold KBig at hbig
  have := core_ineq (nT := D.nT) (a := D.a) (b := D.b) (b' := D.b') (k := D.k) (L := D.L) (La := D.La)
    (B0 := D.B0) (Nc := D.Nc) (M := (m : ℝ)) (sA := D.sumA)
    (lW := umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))) (lk := Real.log D.k)
    (lH := Real.log (1 + D.x ^ C.cHH)) (dI := (1 - D.delBar)⁻¹)
    (et := (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) (Xpp := Xpp)
    (y := D.x ^ D.ε) (yD := D.x ^ (C.eDiv * D.ε)) (yL := D.x ^ (C.eLoss * D.ε)) (K := K)
    (h := 1 + C.cHH) (g := 1 + eK)
    hy hyD hyL hnT ha1 hb0 hba hM hk hMk hMb hL0 hL hLa0 hLa hb' hkb' hX0 hXa hsA0 hsA hB0 hNc hlWk
    hlk0 hlk hlH0 hlH hdI0 hdI het c1 c1' c2 c2' c3 c3' c4 c4' c5 c5' c6 c6' c7 c7'
    (by linarith only [hHH]) (by linarith only [heK]) hbig
  unfold errorTermWith UBar5 MLo5 Data.Vvar Data.LoP ErrText
  exact this

theorem large_x_eventually : LargeXEv := by
  intro ε K cHH eK hε
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ x ^ ε := by
    have hb := (isLittleO_log_rpow_atTop hε).bound (c := 1) one_pos
    filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
    exact (le_abs_self _).trans hx
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, KBig K cHH eK ≤ x ^ ε :=
    (tendsto_rpow_atTop hε).eventually_ge_atTop _
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (h1.and h2)
  exact ⟨x0, fun x hx => hx0 x hx⟩

theorem error_sizes_eventually : ErrorFormsEventual := by
  intro ε K cHH eK hε
  obtain ⟨x0, hx0⟩ := large_x_eventually ε K cHH eK hε
  refine ⟨x0, ?_⟩
  intro U0 _ W _ _ Top _ m f D C Xpp h1 h2 hx hW
  refine error_sizes D C Xpp eK K hW ?_
  rw [h1, h2]
  exact hx0 _ hx

theorem core_lower {nT a b b' k L La B0 Nc M sA lW lk lH dI et Xpp yD yL
    cDiv cE cH cCount cSlope cSl1 cLoss : ℝ}
    (hyD : 0 ≤ yD) (hyL : 0 ≤ yL)
    (hnT : 0 ≤ nT) (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hM : 0 ≤ M) (hk : 0 < k)
    (hL0 : 0 ≤ L) (hLa0 : 0 ≤ La) (hb' : 0 ≤ b') (hX0 : 0 ≤ Xpp)
    (hsA0 : 0 ≤ sA) (hB0 : 0 ≤ B0) (hNc : 0 ≤ Nc)
    (hlW : 0 ≤ lW) (hlk0 : 0 ≤ lk) (hlH0 : 0 ≤ lH) (hdI : 1 ≤ dI) (het : 0 ≤ et)
    (c1 : 0 ≤ cDiv) (c2 : 0 ≤ cE) (c3 : 0 ≤ cH) (c4 : 0 ≤ cCount) (c5 : 0 ≤ cSlope)
    (c6 : 0 ≤ cSl1) (c7 : 0 ≤ cLoss) :
    et ≤ sA * (cCount * (La + M ^ 2 * La / k))
      + (cDiv * nT * a * La + cDiv * M * (B0 + Nc) * yD)
      + M * cE * B0
      + cSlope * nT * a * La * (1 + M / k)
      + lW
      + cLoss * nT * M * b * yL
      + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
          + cSl1 * Xpp + 1)
      + dI * (4 * lH * ((cSlope * nT * a * La * (2 + M / k)
            + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
            + cSl1 * M * B0
            + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
                + cSl1 * Xpp + 1)) + b) + et) := by
  have r1 : 0 ≤ sA * (cCount * (La + M ^ 2 * La / k))
      + (cDiv * nT * a * La + cDiv * M * (B0 + Nc) * yD)
      + M * cE * B0
      + cSlope * nT * a * La * (1 + M / k)
      + lW
      + cLoss * nT * M * b * yL
      + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
          + cSl1 * Xpp + 1) := by positivity
  have r2 : 0 ≤ 4 * lH * ((cSlope * nT * a * La * (2 + M / k)
            + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
            + cSl1 * M * B0
            + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
                + cSl1 * Xpp + 1)) + b) := by positivity
  have r3 := le_mul_of_one_le_left (add_nonneg r2 het) hdI
  linarith only [r1, r2, r3]

theorem error_lower_eta : TraceTermLeErrorTerm := by
  intro U0 _ W _ _ Top _ m f D C Xpp eK K hW hdel0
  obtain ⟨hx, hε, hε1, hb, hxb, hnT, hm, hxm, heK, hk1, hkx, hka, hL0, hL, hLa0, hLa, hb', hkb', hX0,
    hXa, haT, hB0, hNc, hlW, hdel, heta, heB, hC⟩ := hW
  obtain ⟨c1, c1', c2, c2', c3, c3', c4, c4', c5, c5', c6, c6', c7, c7', hD, hLs, hHH⟩ := hC
  have hx0 : 0 < D.x := by linarith only [hx]
  have hb0 : 0 ≤ D.b := by linarith only [hb]
  have ha : 0 ≤ D.a := (mul_nonneg hx0.le hb0).trans hxb
  have hk : 0 < D.k := by linarith only [hk1]
  have hxH : 1 ≤ D.x ^ C.cHH := Real.one_le_rpow hx hHH
  have hdI : 1 ≤ (1 - D.delBar)⁻¹ :=
    (one_le_inv₀ (by linarith only [hdel])).2 (by linarith only [hdel0])
  have hlW0 : 0 ≤ umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ)) :=
    div_nonneg (Finset.sum_nonneg (fun u0 _ => Real.log_natCast_nonneg _)) (Nat.cast_nonneg _)
  have het : 0 ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) := by positivity
  have := core_lower (nT := D.nT) (a := D.a) (b := D.b) (b' := D.b') (k := D.k) (L := D.L) (La := D.La)
    (B0 := D.B0) (Nc := D.Nc) (M := (m : ℝ)) (sA := D.sumA)
    (lW := umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))) (lk := Real.log D.k)
    (lH := Real.log (1 + D.x ^ C.cHH)) (dI := (1 - D.delBar)⁻¹)
    (et := (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) (Xpp := Xpp)
    (yD := D.x ^ (C.eDiv * D.ε)) (yL := D.x ^ (C.eLoss * D.ε))
    (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg hx0.le _) (by linarith only [hnT]) ha hb0
    (Nat.cast_nonneg m) hk hL0 hLa0 hb' hX0 (Finset.sum_nonneg (fun t _ => (haT t).1)) hB0 hNc hlW0
    (Real.log_nonneg hk1) (Real.log_nonneg (by linarith only [hxH])) hdI het c1 c2 c3 c4 c5 c6 c7
  unfold errorTermWith UBar5 MLo5 Data.Vvar Data.LoP
  exact this

noncomputable def modelD (η : ℝ) : Data Unit (fun _ => Unit) Unit 1 1 where
  x := 100000
  ε := 1
  a := 100000
  b := 1
  b' := 1
  k := 100000
  L := 1
  La := 1
  B0 := 1
  Nc := 1
  gam := 0
  LpL := 0
  v := 1
  lg := 0
  logGam := 0
  aT := fun _ => 100000
  w := fun _ _ _ => 1
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 0
  muMaxN := fun _ _ => 0
  h := fun _ _ => 0
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 0
  muMinCC := fun _ => 0
  Fo := fun _ => 0
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun _ => 0
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := η
  eBar := 0

def modelC (cHH : ℝ) : Consts := ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, cHH⟩

lemma model_windows0 (η cHH : ℝ) (hη : 0 ≤ η) (hc : 0 ≤ cHH) :
    ErrWindows0 (modelD η) (modelC cHH) 3 1 1 := by
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨by norm_num [modelD], by norm_num [modelD], by norm_num [modelD], by norm_num [modelD],
    by norm_num [modelD], by simp [Data.nT], by norm_num [modelD], by norm_num [modelD],
    by norm_num, by norm_num [modelD], by norm_num [modelD], by norm_num [modelD],
    by norm_num [modelD], by norm_num [modelD], by norm_num [modelD], by norm_num [modelD],
    by norm_num [modelD], by norm_num [modelD], by norm_num, by norm_num [modelD],
    fun _ => by norm_num [modelD], by norm_num [modelD], by norm_num [modelD], fun _ => ?_,
    by norm_num [modelD], hη, by norm_num [modelD], ?_⟩
  · simp only [Fintype.card_unit, Nat.cast_one, Real.log_one]
    exact mul_nonneg (by norm_num [modelD]) hl2
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hc⟩ <;> norm_num [modelC]

theorem error_windows_model : ErrWindowsModel := by
  refine ⟨modelD (1 / 100000), modelC 1, 3, 1, 1,
    ⟨model_windows0 _ _ (by norm_num) (by norm_num), ?_⟩, ⟨?_, ?_⟩, by norm_num [modelD],
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · norm_num [modelD, modelC, Data.nT]
  · have := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 100000)
    simpa [modelD] using this
  · norm_num [modelD, modelC, KBig]

theorem error_sizes_weak_false : ¬ ErrorFormsWeakWindowsFalse := by
  intro h
  have hw0 := model_windows0 1 10 (by norm_num) (by norm_num)
  have hL : LargeX (modelD 1).x (modelD 1).ε 1 (modelC 10).cHH 1 := by
    refine ⟨?_, ?_⟩
    · have := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 100000)
      simpa [modelD] using this
    · norm_num [modelD, modelC, KBig]
  have h1 := h (modelD 1) (modelC 10) 3 1 1
    ⟨hw0, by norm_num [modelD], by norm_num [modelD]⟩ hL
  have h2 := error_lower_eta (modelD 1) (modelC 10) 3 1 1 hw0 (by norm_num [modelD])
  have h3 := h2.trans h1
  have e10 : (100000 : ℝ) ^ (10 : ℝ) = 100000 ^ (10 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  have e5 : (100000 : ℝ) ^ (((1 : ℝ) + 1 + 3) * 1) = 100000 ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  simp only [modelD, modelC, CErr, ErrText, Data.nT, Real.sqrt_zero, Fintype.card_unit, e10, e5] at h3
  norm_num at h3

theorem text_sizes_windows : TextSizesWindows := by
  intro ε e hε
  have hε3 : 0 < ε / 3 := by positivity
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, (|e| + 1) * Real.log x ≤ x ^ (ε / 3) := by
    have hc : 0 < (|e| + 1)⁻¹ := by positivity
    have hb := (isLittleO_log_rpow_atTop hε3).bound hc
    filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
      Real.norm_of_nonneg (Real.log_nonneg hx1)] at hx
    have : (|e| + 1) * Real.log x ≤ (|e| + 1) * ((|e| + 1)⁻¹ * x ^ (ε / 3)) := by gcongr
    rwa [mul_inv_cancel_left₀ (by positivity)] at this
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (2 * ε / 3) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  obtain ⟨x0, hx0⟩ :=
    Filter.eventually_atTop.1 ((h1.and h2).and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨x0, ?_⟩
  intro x k n lrd hx hk hkx hn hnx hlrd
  obtain ⟨⟨hl, h2x⟩, hx1⟩ := hx0 x hx
  have hxpos : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  obtain ⟨z, hz⟩ : ∃ z, z = x ^ (ε / 3) := ⟨_, rfl⟩
  rw [← hz] at hl hlrd
  have hz0 : 0 ≤ z := by rw [hz]; exact Real.rpow_nonneg hxpos.le _
  have hzz : 2 * z ≤ x ^ ε := by
    have : x ^ ε = x ^ (2 * ε / 3) * z := by
      rw [hz, ← Real.rpow_add hxpos]; congr 1; ring
    rw [this]; gcongr
  have habs : 0 ≤ |e| := abs_nonneg e
  have hxe : x ^ e ≤ Real.exp z := by
    rw [Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.2
    have : Real.log x * e ≤ Real.log x * |e| := by gcongr; exact le_abs_self e
    nlinarith
  have hlogx : Real.log x ≤ z := by nlinarith
  obtain ⟨X, hX⟩ : ∃ X, X = Real.exp z := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = Real.exp (x ^ ε) := ⟨_, rfl⟩
  have hXX : X * X ≤ B := by
    rw [hX, hB, ← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have hX1 : 1 ≤ X := by rw [hX]; exact Real.one_le_exp hz0
  have hX0 : 0 < X := by linarith
  have hB1 : 1 ≤ B := by rw [hB]; exact Real.one_le_exp (Real.rpow_nonneg hxpos.le _)
  have hB0 : 0 < B := by linarith
  have hkX : k ≤ X := by rw [hX]; exact hkx.trans hxe
  have hnX : n ≤ X := by rw [hX]; exact hnx.trans hxe
  have hXB : X ≤ B := (le_mul_of_one_le_left hX0.le hX1).trans hXX
  have hBA : B ≤ x * B := le_mul_of_one_le_left hB0.le hx1
  have hA0 : 0 < x * B := by positivity
  unfold XppTx wppTx bpTx aTx bTx XpTx
  rw [← hz, ← hX, ← hB]
  refine ⟨hx1, hB1, by rw [hB, Real.log_exp], ?_, hkX.trans (hXB.trans hBA), by positivity, ?_, ?_, ?_⟩
  · rw [Real.log_mul hxpos.ne' hB0.ne', hB, Real.log_exp]
    linarith
  · rw [← mul_div_assoc, div_le_iff₀ hX0, mul_comm]
    gcongr
  · positivity
  · have : x * B / (x * B / X / (x * n)) = x * (n * X) := by
      field_simp
    rw [this]
    gcongr
    exact (mul_le_mul_of_nonneg_right hnX hX0.le).trans hXX

theorem error_bound : ErrorFormsEventualUnderSizeParameters := by
  intro ε K cHH eK hε
  obtain ⟨x1, hx1⟩ := error_sizes_eventually ε K cHH eK hε
  obtain ⟨x2, hx2⟩ := text_sizes_windows ε eK hε
  refine ⟨max x1 x2, ?_⟩
  intro U0 _ W _ _ Top _ m f D C Xpp n lrd h1 h2 hx hT
  obtain ⟨tb, ta, tb', tX, tL, tLa, tl0, tl, tn0, tn, tε, tnT, tm, txm, teK, tk1, tkx, taT, tB0, tNc, tW,
    td, te, teB, tet, tC⟩ := hT
  have hk0 : 0 < D.k := by linarith only [tk1]
  rw [h1] at tl
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ :=
    hx2 D.x D.k n lrd ((le_max_right _ _).trans hx) hk0 tkx tn0 tn tl
  rw [← h1] at w2 w3 w4 w5 w6 w7 w8 w9
  rw [← tb] at w2 w3
  rw [← ta] at w4 w5 w7 w9
  rw [← tb'] at w6 w7
  rw [← tX] at w8 w9
  have hxb : D.x * D.b ≤ D.a := by rw [ta, tb]; exact le_refl _
  have hy0 : 0 ≤ D.x ^ D.ε := Real.rpow_nonneg (by linarith only [w1]) _
  have ha1 : 1 ≤ D.a := by
    refine le_trans ?_ hxb
    exact one_le_mul_of_one_le_of_one_le w1 w2
  refine hx1 D C Xpp h1 h2 ((le_max_left _ _).trans hx) ⟨⟨w1, by rw [h1]; exact hε, tε, w2, hxb, tnT, tm,
    txm, teK, tk1, tkx, w5, ?_, ?_, ?_, ?_, w6, w7, w8, w9, taT, tB0, tNc, tW, td, te, teB, tC⟩, tet⟩
  · rw [tL, w3]; exact hy0
  · rw [tL, w3]; linarith only [hy0]
  · rw [tLa]; exact add_nonneg (Real.log_nonneg ha1) tl0
  · rw [tLa]; exact w4

section
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds

theorem size_windows_of_bracket : SizeWindowsOfBracket := by
  intro C ε x n nT nT2 m b k aE Err0 h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, le_refl _, h16⟩

theorem joint_error_bound {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] :
    LeadingTermGrowthJoint (H := H) := by
  intro hTop W _ _ Top _ m f Dd C Xpp eK K D N ell TT T2 a w eT eP hSt hS hDIV hE hH hCount hSl hSlN
    hLo hSI hHH hF hW hX hB0 hNc i1 i2 i3 i4 i5
  have h103 := hSt ⟨0⟩ hS hDIV hE hH hCount hSl hSlN hLo hSI hHH hF
  have hErr := error_sizes Dd C Xpp eK K hW hX
  have hx : 1 ≤ Dd.x := hW.1.1
  have hnT : Dd.nT = (TT.card : ℝ) := by
    unfold Data.nT
    rw [Fintype.card_congr eT, Fintype.card_coe]
  have hbr : ErrText Dd
      ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a := by
    unfold ErrText errorBracketSizeWindows
    rw [hnT]
    gcongr
  refine hTop Dd D N ell TT a w eT eP _ i1 i2 i3 i4 i5 ?_
  have hp : 0 ≤ Dd.x ^ (CErr C * Dd.ε) := Real.rpow_nonneg (by linarith) _
  have := mul_le_mul_of_nonneg_left hbr hp
  linarith

end

end Formalism.LFunctionChainParameters.LErr

section Check
open Formalism.LFunctionChainParameters.LErr
end Check
