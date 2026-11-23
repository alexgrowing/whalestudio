import Formalism.SizeWindowBrackets.TranslateWordBoundHypotheses
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SubThreeMulLogTwoLe
import Formalism.LogVandermondeBounds.HookGammaAmgmMultinomialBounds

open Real

namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer

open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer

lemma nT_nonneg {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
    (D : Data U0 W Top m f) : 0 ≤ D.nT := by
  unfold Data.nT; exact Nat.cast_nonneg _

lemma zTerms_real {cZ cL cU a k mR b' Sc L La lk lkv LZ fR nT sA logT : ℝ}
    (hcZ : 0 ≤ cZ) (hcL : 0 ≤ cL) (hcU : 0 ≤ cU) (ha : 0 ≤ a) (hk : 1 ≤ k) (hmk : mR ≤ k)
    (hb' : 0 ≤ b') (hSc : 0 ≤ Sc) (hL : 0 ≤ L) (hLLa : L ≤ La) (hlk : lk ≤ La) (hlkv : lkv ≤ La)
    (hLZ : LZ ≤ cL * La) (hw1 : fR * k * (b' + Sc) ≤ nT * a) (hw2 : fR * k ^ 2 ≤ nT * a)
    (hn : 0 ≤ nT) (hf : 0 ≤ fR) (hm : 0 ≤ mR) (hs0 : 0 ≤ sA) (hs1 : sA ≤ nT * (2 * a / k))
    (hT : logT ≤ cU * mR * L) :
    sA * logT ≤ 2 * cU * (nT * a * La * (mR / k)) ∧
    cZ * nT * a * lk ≤ cZ * (nT * a * La) ∧
    cZ * fR * k * (b' + Sc) * lk ≤ cZ * (nT * a * La) ∧
    cZ * fR * Sc * logT ≤ cZ * cU * (nT * a * La * (mR / k)) ∧
    cZ * fR * k ^ 2 * LZ ≤ cZ * cL * (nT * a * La) ∧
    cZ * nT * a * lkv ≤ cZ * (nT * a * La) ∧
    cZ * fR * (b' + Sc) * (k * lkv) ≤ cZ * (nT * a * La) ∧
    cZ * fR * (b' + Sc) * logT ≤ cZ * cU * (nT * a * La) := by
  have hk0 : 0 < k := by linarith
  have hLa : 0 ≤ La := le_trans hL hLLa
  have hna : 0 ≤ nT * a := mul_nonneg hn ha
  have hbS : 0 ≤ b' + Sc := add_nonneg hb' hSc
  have hmk' : 0 ≤ mR / k := div_nonneg hm hk0.le
  have hT' : logT ≤ cU * (mR * La) := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLLa hm) hcU
    linarith
  have hcmL : 0 ≤ cU * (mR * La) := mul_nonneg hcU (mul_nonneg hm hLa)
  have hfkb : 0 ≤ fR * k * (b' + Sc) := mul_nonneg (mul_nonneg hf hk0.le) hbS
  have hfb : 0 ≤ fR * (b' + Sc) := mul_nonneg hf hbS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc sA * logT ≤ sA * (cU * (mR * La)) := mul_le_mul_of_nonneg_left hT' hs0
      _ ≤ nT * (2 * a / k) * (cU * (mR * La)) := mul_le_mul_of_nonneg_right hs1 hcmL
      _ = 2 * cU * (nT * a * La * (mR / k)) := by ring
  · have := mul_le_mul_of_nonneg_left hlk (mul_nonneg hcZ hna)
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hlk hfkb
    have h2 := mul_le_mul_of_nonneg_right hw1 hLa
    have := mul_le_mul_of_nonneg_left (le_trans h1 h2) hcZ
    linarith
  · have hfS : 0 ≤ fR * Sc := mul_nonneg hf hSc
    have h1 := mul_le_mul_of_nonneg_left hT' hfS
    have h2 : fR * Sc * k ≤ nT * a := by
      have := mul_nonneg (mul_nonneg hf hk0.le) hb'
      linarith
    have h3 : fR * Sc * (cU * (mR * La)) = cU * ((fR * Sc * k) * (La * (mR / k))) := by
      field_simp
    have h4 : (fR * Sc * k) * (La * (mR / k)) ≤ nT * a * (La * (mR / k)) :=
      mul_le_mul_of_nonneg_right h2 (mul_nonneg hLa hmk')
    have h5 := mul_le_mul_of_nonneg_left h4 hcU
    have h6 : fR * Sc * logT ≤ cU * (nT * a * (La * (mR / k))) := by linarith
    have := mul_le_mul_of_nonneg_left h6 hcZ
    linarith
  · have hfk : 0 ≤ fR * k ^ 2 := mul_nonneg hf (sq_nonneg _)
    have h1 := mul_le_mul_of_nonneg_left hLZ hfk
    have h2 := mul_le_mul_of_nonneg_right hw2 (mul_nonneg hcL hLa)
    have := mul_le_mul_of_nonneg_left (le_trans h1 h2) hcZ
    linarith
  · have := mul_le_mul_of_nonneg_left hlkv (mul_nonneg hcZ hna)
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hlkv hfkb
    have h2 := mul_le_mul_of_nonneg_right hw1 hLa
    have := mul_le_mul_of_nonneg_left (le_trans h1 h2) hcZ
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hT' hfb
    have h2 : fR * (b' + Sc) * mR ≤ nT * a := by
      have := mul_le_mul_of_nonneg_left hmk hfb
      linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (mul_nonneg hcU hLa)
    have h4 : fR * (b' + Sc) * logT ≤ cU * (nT * a * La) := by linarith
    have := mul_le_mul_of_nonneg_left h4 hcZ
    linarith

theorem z_terms : ZTerms := by
  intro U0 W Top _ m f D cZ cL cU Sc LZ logT hW hT
  obtain ⟨hcZ, hcL, hcU, ha, hk, hmk, hb', hSc, haT, hL, hLLa, hlk, hlkv, hLZ, hw1, hw2⟩ := hW
  have hk0 : 0 < D.k := by linarith
  have hn := nT_nonneg D
  have hs0 : 0 ≤ ∑ t, D.aT t / D.k := Finset.sum_nonneg (fun t _ => div_nonneg (haT t).1 hk0.le)
  have hs1 : ∑ t, D.aT t / D.k ≤ D.nT * (2 * D.a / D.k) := by
    have : ∑ t, D.aT t / D.k ≤ ∑ _t : Top, 2 * D.a / D.k :=
      Finset.sum_le_sum (fun t _ => div_le_div_of_nonneg_right (haT t).2 hk0.le)
    simpa [Data.nT, Finset.sum_const, nsmul_eq_mul] using this
  unfold unitZ
  exact zTerms_real hcZ hcL hcU ha hk hmk hb' hSc hL hLLa hlk hlkv hLZ hw1 hw2 hn
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hs0 hs1 hT

theorem z_to_slopes : ZToSlopes := by
  intro U0 W Top _ m f D C cZ cL cU Sc LZ hW hT hZ hC u0 u
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := z_terms D cZ cL cU Sc LZ _ hW (hT u0 u)
  obtain ⟨hcZ, hcL, hcU, ha, hk, hmk, hb', hSc, haT, hL, hLLa, hlk, hlkv, hLZ, hw1, hw2⟩ := hW
  have hk0 : 0 < D.k := by linarith
  have hU : 0 ≤ unitZ D := mul_nonneg (mul_nonneg (nT_nonneg D) ha) (le_trans hL hLLa)
  have hmk' : 0 ≤ (m : ℝ) / D.k := div_nonneg (Nat.cast_nonneg _) hk0.le
  have hUm : 0 ≤ unitZ D * ((m : ℝ) / D.k) := mul_nonneg hU hmk'
  obtain ⟨z1, z2⟩ := hZ u0 u
  have e1 : C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
      = C.cSlope * unitZ D + C.cSlope * (unitZ D * ((m : ℝ) / D.k)) := by unfold unitZ; ring
  have e2 : C.cSlope * D.nT * D.a * D.La = C.cSlope * unitZ D := by unfold unitZ; ring
  have hC1 := mul_le_mul_of_nonneg_right hC hU
  have hC2 := mul_le_mul_of_nonneg_right hC hUm
  unfold cSlopeZ at hC1 hC2
  have p1 : 0 ≤ cZ * cU * unitZ D := mul_nonneg (mul_nonneg hcZ hcU) hU
  have p2 : 0 ≤ cU * unitZ D := mul_nonneg hcU hU
  have p3 : 0 ≤ cZ * unitZ D := mul_nonneg hcZ hU
  have p4 : 0 ≤ cZ * cL * unitZ D := mul_nonneg (mul_nonneg hcZ hcL) hU
  have q3 : 0 ≤ cZ * (unitZ D * ((m : ℝ) / D.k)) := mul_nonneg hcZ hUm
  have q4 : 0 ≤ cZ * cL * (unitZ D * ((m : ℝ) / D.k)) := mul_nonneg (mul_nonneg hcZ hcL) hUm
  constructor
  · rw [e1]
    unfold ZiiR at z1
    linarith
  · rw [e2]
    unfold ZiiiR at z2
    have e3 : cZ * (f : ℝ) * (D.b' + Sc) * (D.k * Real.log (D.k * D.v) + Real.log (D.T u0 u))
        = cZ * (f : ℝ) * (D.b' + Sc) * (D.k * Real.log (D.k * D.v))
          + cZ * (f : ℝ) * (D.b' + Sc) * Real.log (D.T u0 u) := by ring
    linarith

lemma logT_bounds {X Gam y T : ℝ} (hX : 0 < X) (hG : 1 ≤ Gam) (hy : 0 < y)
    (h1 : X * Gam ^ (-(2 / y)) ≤ T) (h2 : T ≤ X * Gam ^ (-(2 / y)) * (1 + 1 / y)) :
    Real.log X - 2 * Real.log Gam / y ≤ Real.log T ∧
    Real.log T ≤ Real.log X - 2 * Real.log Gam / y + 1 / y := by
  have hG0 : 0 < Gam := by linarith
  have hp : 0 < Gam ^ (-(2 / y)) := Real.rpow_pos_of_pos hG0 _
  have hS : 0 < X * Gam ^ (-(2 / y)) := mul_pos hX hp
  have hT : 0 < T := lt_of_lt_of_le hS h1
  have hy1 : 0 < 1 + 1 / y := by positivity
  have e : Real.log (X * Gam ^ (-(2 / y))) = Real.log X - 2 * Real.log Gam / y := by
    rw [Real.log_mul hX.ne' hp.ne', Real.log_rpow hG0]; ring
  constructor
  · rw [← e]; exact Real.log_le_log hS h1
  · have h3 := Real.log_le_log hT h2
    rw [Real.log_mul hS.ne' hy1.ne', e] at h3
    have h4 := Real.log_le_sub_one_of_pos hy1
    linarith

section
variable {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ}

lemma fk_pos {D : Data U0 W Top m f} {c5 Gam : ℝ} (hW : CountWindows D c5 Gam) :
    0 < (f : ℝ) * D.k ∧ 1 / ((f : ℝ) * D.k) ≤ 1 := by
  obtain ⟨_, hf, hk, _⟩ := hW
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have h1 : 1 ≤ (f : ℝ) * D.k := by nlinarith
  exact ⟨by linarith, by rw [div_le_one (by linarith)]; exact h1⟩

lemma logT_of_window {D : Data U0 W Top m f} {c5 Gam : ℝ} {X : ∀ u0, W u0 → ℝ}
    (hW : CountWindows D c5 Gam) (hLW : LevelWindow D Gam X) (u0 : U0) (u : W u0) :
    Real.log (X u0 u) - 2 * D.logGam / ((f : ℝ) * D.k) ≤ Real.log (D.T u0 u) ∧
    Real.log (D.T u0 u) ≤ Real.log (X u0 u) - 2 * D.logGam / ((f : ℝ) * D.k) + 1 / ((f : ℝ) * D.k) := by
  obtain ⟨hX, h1, h2⟩ := hLW u0 u
  have hy := (fk_pos hW).1
  obtain ⟨_, _, _, hG, hlG, _⟩ := hW
  rw [hlG]
  exact logT_bounds hX hG hy h1 h2

end

theorem proposition_to_log_t_upper : Prop5ToLogTUp := by
  intro U0 W Top m f D c5 Gam X hW h5 hLW u0 u
  obtain ⟨_, hu⟩ := logT_of_window hW hLW u0 u
  obtain ⟨hy, hy1⟩ := fk_pos hW
  obtain ⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩ := hW
  have hg : 0 ≤ 2 * D.logGam / ((f : ℝ) * D.k) := by
    rw [hlG]; exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hG)) hy.le
  have := (h5 u0 u).2
  have e : (c5 + 1) * (m : ℝ) * D.L = c5 * (m : ℝ) * D.L + (m : ℝ) * D.L := by ring
  rw [e]; linarith

theorem proposition_to_count_general : Prop5ToCount := by
  intro U0 W Top m f D C c5 Gam X hW h5 hV hLW hC u0 u
  have hup := proposition_to_log_t_upper D c5 Gam X hW h5 hLW
  obtain ⟨hl, hu⟩ := logT_of_window hW hLW u0 u
  obtain ⟨hy, hy1⟩ := fk_pos hW
  have hW' := hW
  obtain ⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩ := hW
  have hk0 : 0 < D.k := by linarith
  have hq : 0 ≤ D.L + (m : ℝ) ^ 2 * D.L / D.k :=
    add_nonneg hL (div_nonneg (mul_nonneg (sq_nonneg _) hL) hk0.le)
  rw [hC]
  refine ⟨?_, hup u0 u, ?_⟩
  · have := (h5 u0 u).1
    unfold mainCount at this
    have e : (c5 + 1) * (D.L + (m : ℝ) ^ 2 * D.L / D.k)
        = c5 * (D.L + (m : ℝ) ^ 2 * D.L / D.k) + (D.L + (m : ℝ) ^ 2 * D.L / D.k) := by ring
    rw [e]; linarith
  · intro u'
    obtain ⟨hl', hu'⟩ := logT_of_window hW' hLW u0 u'
    have hv := abs_le.mp (hV u0 u u')
    have e : (c5 + 1) * Real.log D.k = c5 * Real.log D.k + Real.log D.k := by ring
    rw [e]
    exact abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩

theorem proposition_to_count : Prop5ToCount5 := by
  intro U0 W Top m f D C c5 Gam X hW h5 hV hLW hC
  have hCount : D.Count { C with cCount := c5 + 1 } :=
    proposition_to_count_general D { C with cCount := c5 + 1 } c5 Gam X hW h5 hV hLW rfl
  obtain ⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩ := hW
  have hk0 : 0 < D.k := by linarith
  have hq0 : 0 ≤ (m : ℝ) ^ 2 / D.k := div_nonneg (sq_nonneg _) hk0.le
  have e1 : (m : ℝ) ^ 2 * D.L / D.k = (m : ℝ) ^ 2 / D.k * D.L := by ring
  have e2 : (m : ℝ) ^ 2 * D.La / D.k = (m : ℝ) ^ 2 / D.k * D.La := by ring
  have e3 : 2 * D.logGam / ((f : ℝ) * D.k) = 2 * (D.logGam / ((f : ℝ) * D.k)) := by ring
  have hmL' : (m : ℝ) ^ 2 / D.k * D.L ≤ (m : ℝ) ^ 2 / D.k * D.La := mul_le_mul_of_nonneg_left hLLa hq0
  have hmLa : 0 ≤ (m : ℝ) ^ 2 / D.k * D.La := mul_nonneg hq0 (by linarith)
  have hq : 0 ≤ D.La + (m : ℝ) ^ 2 / D.k * D.La := by linarith
  have hsum : D.L + (m : ℝ) ^ 2 / D.k * D.L ≤ D.La + (m : ℝ) ^ 2 / D.k * D.La := by linarith
  have hcs := mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ c5 + 1)
  intro u0 u
  obtain ⟨h1, h2, h3⟩ := hCount u0 u
  refine ⟨?_, ?_, ?_⟩
  · have h1' : _ - (c5 + 1) * (D.L + (m : ℝ) ^ 2 * D.L / D.k) - 2 * D.logGam / ((f : ℝ) * D.k) ≤ _ := h1
    rw [e1, e3] at h1'
    rw [e2]
    have := mul_le_mul_of_nonneg_right hC hq
    have e4 : (c5 + 3) * (D.La + (m : ℝ) ^ 2 / D.k * D.La)
        = (c5 + 1) * (D.La + (m : ℝ) ^ 2 / D.k * D.La) + 2 * (D.La + (m : ℝ) ^ 2 / D.k * D.La) := by ring
    linarith
  · have h2' : _ ≤ (c5 + 1) * (m : ℝ) * D.L := h2
    have := mul_le_mul_of_nonneg_right (by linarith : c5 + 1 ≤ C.cCount) (by linarith : 0 ≤ (m : ℝ) * D.L)
    linarith
  · intro u'
    have h3' : _ ≤ (c5 + 1) * Real.log D.k := h3 u'
    have := mul_le_mul_of_nonneg_right (by linarith : c5 + 1 ≤ C.cCount) (by linarith : 0 ≤ Real.log D.k)
    linarith

theorem level_lower_of_count : LevelLowerOfCount := by
  intro U0 W Top m f D c5 Gam X hW h5 hLW hw hlg hmk hL1 hcm u0 u
  obtain ⟨hl, _⟩ := logT_of_window hW hLW u0 u
  obtain ⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩ := hW
  have hk0 : 0 < D.k := by linarith
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have h1 := (h5 u0 u).1
  have hs : 0 ≤ ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun ρ _ => Real.log_nonneg (hw u0 j ρ))))
  have hmc : 16 * ((m : ℝ) * D.L) ≤ mainCount D u0 := by
    unfold mainCount
    have := mul_le_mul_of_nonneg_left hlg hm
    linarith
  have hq : (m : ℝ) ^ 2 * D.L / D.k ≤ D.L := by
    rw [div_le_iff₀ hk0]
    have := mul_le_mul_of_nonneg_right hmk hL
    linarith
  have hq2 := mul_le_mul_of_nonneg_left hq hc
  have e3 : 2 * D.logGam / ((f : ℝ) * D.k) = 2 * (D.logGam / ((f : ℝ) * D.k)) := by ring
  have hcl : (2 * c5 + 2) * D.L ≤ 15 * (m : ℝ) * D.L := mul_le_mul_of_nonneg_right hcm hL
  have hmL0 : 0 ≤ (m : ℝ) * D.L := mul_nonneg hm hL
  nlinarith

theorem level_sizes : LevelSizes := by
  intro f m b T N hf hm hb hT hN hN2
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hm3 : (3 : ℝ) ≤ (m : ℝ) / 2 := by
    have : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hb3 : b ^ 3 ≤ T := by
    have h := Real.rpow_le_rpow_of_exponent_le hb1 hm3
    have e : b ^ (3 : ℝ) = b ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e] at h
    linarith
  have h4f : 4 * (f : ℝ) ≤ T := by nlinarith
  have hT2 : 2 < T := by linarith
  have hT0 : 0 < T := by linarith
  have hA : 4 * (f : ℝ) / T * b ^ 2 ≤ 1 / 2 := by
    have e : 4 * (f : ℝ) / T * b ^ 2 = 4 * (f : ℝ) * b ^ 2 / T := by ring
    rw [e, div_le_iff₀ hT0]
    have : 8 * (f : ℝ) * b ^ 2 ≤ b * b ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    nlinarith
  have hB : (f : ℝ) * Real.log (T - 1) / (T - 2) ≤ 1 / 2 := by
    have hy : 0 < T - 1 := by linarith
    set s := Real.sqrt (T - 1) with hs
    have hs2 : s ^ 2 = T - 1 := Real.sq_sqrt hy.le
    have h8 : (8 * (f : ℝ)) ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ (by positivity) hb 3
    have hs8 : 8 * (f : ℝ) ≤ s := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [mul_nonneg (sq_nonneg (f : ℝ)) (by linarith : (0 : ℝ) ≤ (f : ℝ) - 1)]
    have hs0 : 0 < s := by linarith
    have hlog : Real.log (T - 1) ≤ 2 * s := by
      have h1 := Real.log_le_sub_one_of_pos hs0
      have h2 : Real.log s = Real.log (T - 1) / 2 := Real.log_sqrt hy.le
      linarith
    rw [div_le_iff₀ (by linarith)]
    have h3 : (f : ℝ) * Real.log (T - 1) ≤ (f : ℝ) * (2 * s) :=
      mul_le_mul_of_nonneg_left hlog (by linarith)
    nlinarith
  refine ⟨hT2, h4f, ?_, by linarith⟩
  rw [div_le_iff₀ hT0]; linarith

theorem pow_of_log : PowOfLog := by
  intro mR b T hb hT
  have hp : 0 < b ^ (mR / 2) := Real.rpow_pos_of_pos hb _
  rw [← Real.log_le_log_iff hp hT, Real.log_rpow hb]
  constructor <;> intro h <;> linarith

lemma bernoulli_level (f : ℕ) {T : ℝ} (hT : 2 ≤ T) :
    1 - (f : ℝ) / (T - 1) ≤ (1 - 1 / (T - 1)) ^ f := by
  have hy : 0 < T - 1 := by linarith
  have h1 : 1 / (T - 1) ≤ 1 := by rw [div_le_one hy]; linarith
  have h := one_add_mul_le_pow (a := -(1 / (T - 1))) (by linarith) f
  have e1 : 1 + (f : ℝ) * -(1 / (T - 1)) = 1 - (f : ℝ) / (T - 1) := by ring
  have e2 : 1 + -(1 / (T - 1)) = 1 - 1 / (T - 1) := by ring
  rw [e1, e2] at h
  exact h

theorem defect_bound_alt : DefectBound := by
  intro f T hT
  have h := bernoulli_level f hT
  have hy : 0 < T - 1 := by linarith
  have hT0 : 0 < T := by linarith
  have hf : (0 : ℝ) ≤ (f : ℝ) := Nat.cast_nonneg _
  have h2 : (f : ℝ) / (T - 1) ≤ 2 * (f : ℝ) / T := by
    rw [div_le_div_iff₀ hy hT0]; nlinarith
  linarith

theorem index_to_lambda : IndexToLengthBound := by
  intro U0 W Top _ m f D aM VV Wt bt hW
  obtain ⟨hk, hkb, ha, haM, hWt, hbt⟩ := hW
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hb' : 0 ≤ D.b' := by linarith
  have hak : 0 ≤ D.a / D.k := div_nonneg ha hk.le
  have haMk : aM / D.k ≤ 2 * (D.a / D.k) := by
    have := div_le_div_of_nonneg_right haM hk.le
    have e : 2 * D.a / D.k = 2 * (D.a / D.k) := by ring
    linarith
  have hcard : ((VV.card : ℕ) : ℝ) ≤ D.nT := by
    unfold Data.nT
    exact_mod_cast Finset.card_le_univ VV
  have h1 : ∑ t ∈ VV, ((aM / D.k + 2 * Wt t + D.k) + bt t) ≤ ∑ _t ∈ VV, 7 * (D.a / D.k + D.b') :=
    Finset.sum_le_sum (fun t _ => by have := hWt t; have := hbt t; linarith)
  rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib] at h1
  have h2 : ((VV.card : ℕ) : ℝ) * (7 * (D.a / D.k + D.b')) ≤ D.nT * (7 * (D.a / D.k + D.b')) :=
    mul_le_mul_of_nonneg_right hcard (by linarith)
  have h3 := mul_le_mul_of_nonneg_left (le_trans h1 h2) hm
  unfold lambdaIndex
  linarith

theorem joint_four_five : SlopeCountJoint := by
  intro U0 W Top _ m f D C cZ cL Sc LZ c5 Gam X hZW hZ hCW h5 hV hLW hC1 hC2
  exact ⟨z_to_slopes D C cZ cL (c5 + 1) Sc LZ hZW (proposition_to_log_t_upper D c5 Gam X hCW h5 hLW) hZ hC1,
    proposition_to_count D C c5 Gam X hCW h5 hV hLW hC2⟩

lemma text_key (ε E : ℝ) (hε : 0 < ε) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    8 ≤ x ∧ Real.log (bTx x ε) = x ^ ε ∧ 0 < bTx x ε ∧ 0 < aTx x ε ∧ 0 < bpTx x ε ∧
    ∀ K : ℝ, 0 < K → K ≤ x ^ E → K ≤ aTx x ε ∧ K * bpTx x ε ≤ aTx x ε ∧ x * K ≤ bpTx x ε := by
  obtain ⟨x₀, h⟩ := text_sizes_windows ε E hε
  refine ⟨max x₀ 8, fun x hx => ?_⟩
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx8 : 8 ≤ x := le_trans (le_max_right _ _) hx
  have hxp : 0 < x := by linarith
  have hb : 0 < bTx x ε := Real.exp_pos _
  have ha : 0 < aTx x ε := mul_pos hxp hb
  have hbp : 0 < bpTx x ε := div_pos ha (Real.exp_pos _)
  have hl : Real.log (bTx x ε) = x ^ ε := Real.log_exp _
  refine ⟨hx8, hl, hb, ha, hbp, fun K hK hKE => ?_⟩
  obtain ⟨_, _, _, _, k1, _, k2, _, k3⟩ :=
    h x K K 0 hx0 hK hKE hK hKE (Real.rpow_nonneg hxp.le _)
  refine ⟨k1, k2, ?_⟩
  have hxK : 0 < x * K := mul_pos hxp hK
  have hw : 0 < wppTx x ε K := div_pos hbp hxK
  unfold XppTx at k3
  rw [div_le_iff₀ hw] at k3
  have h1 : 1 ≤ wppTx x ε K := by
    by_contra hlt
    rw [not_le] at hlt
    have := mul_lt_mul_of_pos_left hlt ha
    linarith
  unfold wppTx at h1
  rwa [le_div_iff₀ hxK, one_mul] at h1

theorem small_terms_bound₂ : SmallText := by
  intro ε e cT c6 hε he hc6
  obtain ⟨x₀, h⟩ := text_key ε (e + 2) hε
  refine ⟨max x₀ (2 * |cT| / c6 + 1), fun x k nT hx hn0 hn hk hnk => ?_⟩
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 2 * |cT| / c6 + 1 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hx8, _, _, ha, hbp, hK⟩ := h x hx0
  have hxp : 0 < x := by linarith
  have hKp : 0 < x ^ (e + 2) := Real.rpow_pos_of_pos hxp _
  obtain ⟨_, k2, _⟩ := hK _ hKp le_rfl
  have hXp : 0 < XpTx x ε := Real.exp_pos _
  have hKX : x ^ (e + 2) ≤ XpTx x ε := by
    unfold bpTx at k2
    rw [← mul_div_assoc, div_le_iff₀ hXp] at k2
    have : x ^ (e + 2) * aTx x ε ≤ XpTx x ε * aTx x ε := by linarith
    exact le_of_mul_le_mul_right this ha
  have hxe : 0 < x ^ e := Real.rpow_pos_of_pos hxp _
  have eK : x ^ (e + 2) = x ^ e * x ^ 2 := by
    rw [Real.rpow_add hxp, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have q1 : nT * (x / k) ≤ 1 / x := by
    rw [← mul_div_assoc, div_le_div_iff₀ hk hxp]; nlinarith
  have q2 : nT * (x / XpTx x ε) ≤ 1 / x := by
    rw [← mul_div_assoc, div_le_div_iff₀ hXp hxp]
    have : nT * x * x ≤ x ^ e * x ^ 2 := by
      have := mul_le_mul_of_nonneg_right hn (sq_nonneg x)
      nlinarith
    linarith
  have q0 : 0 ≤ nT * (x / k + x / XpTx x ε) :=
    mul_nonneg hn0 (add_nonneg (div_nonneg hxp.le hk.le) (div_nonneg hxp.le hXp.le))
  have q3 : nT * (x / k + x / XpTx x ε) ≤ 2 / x := by
    have : 2 / x = 1 / x + 1 / x := by ring
    rw [this, mul_add]; linarith
  have h1 : cT * nT * (x / k + x / XpTx x ε) ≤ |cT| * (2 / x) := by
    calc cT * nT * (x / k + x / XpTx x ε) = cT * (nT * (x / k + x / XpTx x ε)) := by ring
      _ ≤ |cT| * (nT * (x / k + x / XpTx x ε)) := mul_le_mul_of_nonneg_right (le_abs_self _) q0
      _ ≤ |cT| * (2 / x) := mul_le_mul_of_nonneg_left q3 (abs_nonneg _)
  have h2 : |cT| * (2 / x) < c6 := by
    rw [← mul_div_assoc, div_lt_iff₀ hxp]
    have : 2 * |cT| / c6 < x := by linarith
    rw [div_lt_iff₀ hc6] at this
    linarith
  linarith

set_option maxHeartbeats 1000000 in
theorem analytic_bounds_eventual : ExponentialPowerWindows := by
  intro ε e hε he
  obtain ⟨x₀, h⟩ := text_key ε (4 * e + 2) hε
  refine ⟨x₀, ?_⟩
  intro x k fR mR nT N Sc lrd v hx hk1 hk hf1 hf hm1 hm hN1 hN hn1 hSc0 hSc hv hlv hlrd
  obtain ⟨hx8, hlb, hb, ha, hbp, hK⟩ := h x hx
  have hxp : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx2 : 64 ≤ x ^ 2 := by nlinarith
  have hxx : x ≤ x ^ 2 := by nlinarith
  have h8x : 8 * x ≤ x ^ 2 := by nlinarith
  set y := x ^ e with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1 he
  have hE : x ^ (4 * e + 2) = y ^ 4 * x ^ 2 := by
    rw [Real.rpow_add hxp, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hy,
      ← Real.rpow_natCast (x ^ e) 4, ← Real.rpow_mul hxp.le]
    congr 2
    push_cast; ring
  rw [hE] at hK
  have hk0 : 0 < k := by linarith
  have hf0 : 0 < fR := by linarith
  have hm0 : 0 < mR := by linarith
  have hN0 : 0 < N := by linarith
  have hy0 : 0 < y := by linarith
  have y2 : y ^ 2 ≤ y ^ 4 := pow_le_pow_right₀ hy1 (by norm_num)
  have y3 : y ^ 3 ≤ y ^ 4 := pow_le_pow_right₀ hy1 (by norm_num)
  have y1 : y ≤ y ^ 4 := by simpa using pow_le_pow_right₀ hy1 (by norm_num : 1 ≤ 4)
  have y4 : 0 < y ^ 4 := by positivity
  have big : ∀ {K c : ℝ}, K ≤ c * y ^ 4 → c ≤ x ^ 2 → K ≤ y ^ 4 * x ^ 2 := by
    intro K c h1 h2
    have := mul_le_mul_of_nonneg_right h2 y4.le
    linarith
  have p2 : fR * k ≤ y ^ 2 := by
    have : fR * k ≤ y * y := mul_le_mul hf hk hk0.le hy0.le
    linarith [sq y]
  have pm2 : mR * k ≤ y ^ 2 := by
    have : mR * k ≤ y * y := mul_le_mul hm hk hk0.le hy0.le
    linarith [sq y]
  have pmN : mR * N ≤ y ^ 2 := by
    have : mR * N ≤ y * y := mul_le_mul hm hN hN0.le hy0.le
    linarith [sq y]
  have p3 : fR * k ^ 2 ≤ y ^ 3 := by
    have : fR * k * k ≤ y ^ 2 * y := mul_le_mul p2 hk hk0.le (by positivity)
    have e1 : fR * k ^ 2 = fR * k * k := by ring
    have e2 : y ^ 3 = y ^ 2 * y := by ring
    linarith
  have pmNk : mR * N * k ≤ y ^ 3 := by
    have : mR * N * k ≤ y ^ 2 * y := mul_le_mul pmN hk hk0.le (by positivity)
    have e2 : y ^ 3 = y ^ 2 * y := by ring
    linarith
  have p4 : fR * (mR * N * k) ≤ y ^ 4 := by
    have : fR * (mR * N * k) ≤ y * y ^ 3 := mul_le_mul hf pmNk (by positivity) hy0.le
    have e2 : y ^ 4 = y * y ^ 3 := by ring
    linarith
  obtain ⟨A1, _, A3⟩ := hK k hk0 (big (c := 1) (by linarith) (by linarith))
  obtain ⟨_, B2, _⟩ := hK (2 * (fR * k)) (by positivity) (big (c := 2) (by linarith) (by linarith))
  obtain ⟨C1, _, _⟩ := hK (fR * k ^ 2) (by positivity) (big (c := 1) (by linarith) (by linarith))
  obtain ⟨D1, _, _⟩ := hK (fR * (mR * N * k)) (by positivity) (big (c := 1) (by linarith) (by linarith))
  obtain ⟨_, E2, _⟩ := hK (mR * k) (by positivity) (big (c := 1) (by linarith) (by linarith))
  obtain ⟨F1, _, _⟩ := hK (mR * N * k) (by positivity) (big (c := 1) (by linarith) (by linarith))
  obtain ⟨G1, _, _⟩ := hK (8 * x * fR) (by positivity) (by
    have := mul_le_mul h8x (le_trans hf y1) hf0.le (by positivity)
    linarith)
  obtain ⟨H1, _, _⟩ := hK (x * (mR * N)) (by positivity) (by
    have := mul_le_mul hxx (le_trans pmN y2) (by positivity) (by positivity)
    linarith)
  obtain ⟨_, I2, _⟩ := hK (x * mR) (by positivity) (by
    have := mul_le_mul hxx (le_trans hm y1) hm0.le (by positivity)
    linarith)
  have hax : aTx x ε = x * bTx x ε := rfl
  have hna : aTx x ε ≤ nT * aTx x ε := le_mul_of_one_le_left ha.le hn1
  have hak : 0 < aTx x ε / k := div_pos ha hk0
  have hlk : Real.log k ≤ Real.log (aTx x ε) := Real.log_le_log hk0 A1
  refine ⟨by linarith, ?_, ?_, ?_, ?_, ?_, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.log_mul hk0.ne' hv.ne']; linarith
  · rw [Real.log_mul ha.ne' hv.ne']; linarith
  · have : Real.log (bTx x ε) ≤ Real.log (aTx x ε) := Real.log_le_log hb (by rw [hax]; exact le_mul_of_one_le_left hb.le hx1)
    linarith
  · rw [hlb]; exact Real.one_le_rpow hx1 hε.le
  · have : fR * k * (bpTx x ε + Sc) ≤ fR * k * (bpTx x ε + bpTx x ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · exact le_trans (le_mul_of_one_le_left hk0.le hx1) A3
  · have : fR * mR * N ≤ aTx x ε / k := by rw [le_div_iff₀ hk0]; linarith
    exact le_trans this (le_mul_of_one_le_left hak.le hn1)
  · rw [le_div_iff₀ hk0]; linarith
  · rw [le_div_iff₀ hk0]; linarith
  · rw [hax] at G1
    have : x * (8 * fR) ≤ x * bTx x ε := by linarith
    exact le_of_mul_le_mul_left this hxp
  · rw [hax] at H1
    exact le_of_mul_le_mul_left H1 hxp
  · rw [hax] at I2
    have : x * (mR * bpTx x ε) ≤ x * bTx x ε := by linarith
    exact le_of_mul_le_mul_left this hxp

theorem exact_coefficient_difference : ExactCoeffDiff := by
  intro U0 W Top m f D bN hW u0
  obtain ⟨hf, hm1, hmk, hmx, hL, hv, hl0, hl1, hl2, hlg, hb⟩ := hW
  have hf0 : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hk0 : 0 < D.k := by linarith
  have hvp : 0 < D.v / π := div_pos hv Real.pi_pos
  have h1 : ∀ j ρ, Real.log (D.w u0 j ρ * D.v / π) = Real.log (D.w u0 j ρ) + Real.log (D.v / π) := by
    intro j ρ
    rw [mul_div_assoc, Real.log_mul (hb u0 j ρ).2.1.ne' hvp.ne']
  have h2 : (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π))
      = (1 / (f : ℝ)) * (∑ ρ : Fin f, ∑ j : Fin m, Real.log (D.w u0 j ρ)) + (m : ℝ) * Real.log (D.v / π) := by
    simp_rw [h1]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have h3 : (∑ ρ : Fin f, ∑ j : Fin m, (Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ)))
      = (∑ ρ : Fin f, ∑ j : Fin m, Real.log (D.w u0 j ρ))
        - ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ) := by
    simp only [Finset.sum_sub_distrib]
  unfold mainCount exactMain
  rw [h2, h3]
  field_simp
  ring

theorem exact_coefficient_price : ExactCoeffPrice := by
  intro U0 W Top m f D bN hW u0
  have hd := exact_coefficient_difference D bN hW u0
  obtain ⟨hf, hm1, hmk, hmx, hL, hv, hl0, hl1, hl2, hlg, hb⟩ := hW
  have hf0 : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hk0 : 0 < D.k := by linarith
  have hx0 : 0 < D.x := by linarith
  have hq0 : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) / (2 * D.k) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hr0 : 0 ≤ ((m : ℝ) - 1) / (2 * D.k) := div_nonneg (by linarith) (by linarith)
  have hr1 : ((m : ℝ) - 1) / (2 * D.k) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have t1 : (1 - (m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * Real.log (D.v / π) ≤ D.L := by
    have := mul_nonneg hq0 hl0
    linarith
  have t2 : (((m : ℝ) - 1) / (2 * D.k)) * Real.log (2 * D.v) ≤ 1 / 2 * D.L := by
    calc (((m : ℝ) - 1) / (2 * D.k)) * Real.log (2 * D.v) ≤ (((m : ℝ) - 1) / (2 * D.k)) * D.L :=
          mul_le_mul_of_nonneg_left hl2 hr0
      _ ≤ 1 / 2 * D.L := mul_le_mul_of_nonneg_right hr1 (by linarith)
  have t3 : 0 ≤ ((m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * D.lg := mul_nonneg hq0 hlg
  have t4 : (1 / (f : ℝ)) * ∑ ρ : Fin f, ∑ j : Fin m, (Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ)) ≤ 1 := by
    have hterm : ∀ (ρ : Fin f) (j : Fin m), Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ) ≤ 1 / D.x := by
      intro ρ j
      obtain ⟨b0, w0, wb, _⟩ := hb u0 j ρ
      have h1x : 0 < 1 + 1 / D.x := by positivity
      have := Real.log_le_log w0 wb
      rw [Real.log_mul b0.ne' h1x.ne'] at this
      have := Real.log_le_sub_one_of_pos h1x
      linarith
    have hs : ∑ ρ : Fin f, ∑ j : Fin m, (Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ))
        ≤ ∑ _ρ : Fin f, ∑ _j : Fin m, 1 / D.x :=
      Finset.sum_le_sum (fun ρ _ => Finset.sum_le_sum (fun j _ => hterm ρ j))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have h5 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1 / (f : ℝ))
    have e : 1 / (f : ℝ) * ((f : ℝ) * ((m : ℝ) * (1 / D.x))) = (m : ℝ) / D.x := by field_simp
    rw [e] at h5
    have : (m : ℝ) / D.x ≤ 1 := by rw [div_le_one hx0]; exact hmx
    linarith
  have t5 : (1 / D.k) * ((1 / (f : ℝ)) * ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ)) ≤ 2 * D.L := by
    have hs : ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ) ≤ ∑ _ρ : Fin f, ∑ _j : Fin m, 2 * D.L :=
      Finset.sum_le_sum (fun ρ _ => Finset.sum_le_sum (fun j _ => (hb u0 j ρ).2.2.2))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have h5 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1 / (f : ℝ))
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 1 / D.k)
    have e : 1 / D.k * (1 / (f : ℝ) * ((f : ℝ) * ((m : ℝ) * (2 * D.L)))) = (m : ℝ) / D.k * (2 * D.L) := by
      field_simp
    rw [e] at h6
    have h7 : (m : ℝ) / D.k ≤ 1 := by rw [div_le_one hk0]; exact hmk
    have h8 := mul_le_mul_of_nonneg_right h7 (by linarith : 0 ≤ 2 * D.L)
    linarith
  linarith

theorem exact_coefficient_to_proposition : ExactCoeffToProp5 := by
  intro U0 W Top m f D cE c5 X bN hW hE hU hc5 hc u0 u
  have hp := exact_coefficient_price D bN hW u0
  obtain ⟨hf, hm1, hmk, hmx, hL, hv, hl0, hl1, hl2, hlg, hb⟩ := hW
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hk0 : 0 < D.k := by linarith
  refine ⟨?_, hU u0 u⟩
  have h1 := hE u0 u
  have hq : 0 ≤ (m : ℝ) ^ 2 * D.L / D.k := div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hk0.le
  have h2 : (cE + 6) * D.L ≤ c5 * D.L := mul_le_mul_of_nonneg_right hc (by linarith)
  have h3 := mul_nonneg hc5 hq
  have e : c5 * (D.L + (m : ℝ) ^ 2 * D.L / D.k) = c5 * D.L + c5 * ((m : ℝ) ^ 2 * D.L / D.k) := by ring
  rw [e]; linarith

namespace Model

noncomputable def gv : ℝ := Real.exp 1 ^ (-(2 / (((2 : ℕ) : ℝ) * Real.exp 2)))

noncomputable def Xv : ∀ _ : Unit, Fin 2 → ℝ := fun _ u => Real.exp (13 + ((u : ℕ) : ℝ))

noncomputable def D0 : Data Unit (fun _ => Fin 2) Unit 6 2 where
  x := 6
  ε := 1
  a := Real.exp 40
  b := Real.exp 4
  b' := Real.exp 2
  k := Real.exp 2
  L := 4
  La := 100
  B0 := 2 * 6 * Real.exp 4 * 4
  Nc := 0
  gam := 0
  LpL := 0
  v := π
  lg := 0
  logGam := 1
  aT := fun _ => Real.exp 40
  w := fun _ _ _ => 1
  d := fun _ _ => 1
  T := fun _ u => Xv () u * gv
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
  HH := fun _ => 0
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0

noncomputable def D1 : Data Unit (fun _ => Fin 2) Unit 6 2 :=
  { D0 with
    muM := fun u0 u => ZiiR D0 1 1 1 (Real.log (D0.T u0 u))
    muMaxM := fun u0 u => ZiiiR D0 1 1 1 (Real.log (D0.T u0 u)) }

lemma h6 : (6 : ℝ) ≤ Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [e]; nlinarith

lemma exp_forty_eq : Real.exp 40 = Real.exp 2 * Real.exp 2 * Real.exp 36 := by
  rw [← Real.exp_add, ← Real.exp_add]; norm_num

lemma hak : Real.exp 40 / Real.exp 2 = Real.exp 2 * Real.exp 36 := by
  rw [exp_forty_eq]; field_simp

end Model

end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
