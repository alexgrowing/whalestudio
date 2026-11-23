import Formalism.FlagUnipotentLattices.CuspidalityThreshold
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CoefficientLeOperatorNorm
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.NearFarVolumeBounds

open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory NumberField
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix

namespace Formalism.HermitianLatticeCounting.P

theorem threshold_cusp_numeric : CuspidalityThreshold := by
  intro n q h hq hqn hh
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hqn' : 2 * (q:ℝ) ≤ n := by exact_mod_cast hqn
  have e : Real.sqrt (2 * (q : ℝ)) = Real.sqrt 2 * Real.sqrt q := Real.sqrt_mul (by norm_num) _
  rw [e]
  set r := Real.sqrt 2 with hr
  set s := Real.sqrt (q:ℝ) with hs'
  have r2 : r * r = 2 := Real.mul_self_sqrt (by norm_num)
  have s2 : s * s = q := Real.mul_self_sqrt (by linarith)
  have r0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have s1 : 1 ≤ s := by rw [hs']; exact Real.one_le_sqrt.mpr hq'
  have rU : r < 1.415 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hns : 2 * s ≤ n := by nlinarith
  have hn0 : (0:ℝ) < n := by linarith
  rw [lt_div_iff₀ (by positivity)]
  have key : (2 * (n:ℝ) * (r * s) + 2 * (n:ℝ) ^ 2) * (r * s)
      = 2 * n * (r * r) * (s * s) + 2 * (n:ℝ) ^ 2 * r * s := by ring
  rw [key, r2]
  have a1 : 2 * (n:ℝ) * 2 * (s * s) ≤ 2 * (n:ℝ) ^ 2 * s := by
    have : (n:ℝ) * s * (2 * s) ≤ (n:ℝ) * s * n := by gcongr
    nlinarith
  have a2 : 2 * (n:ℝ) ^ 2 * r * s < 2.83 * ((n:ℝ) ^ 2 * s) := by
    have : 0 < (n:ℝ) ^ 2 * s := by positivity
    nlinarith
  have a3 : 0 < (n:ℝ) ^ 2 * s := by positivity
  nlinarith

lemma rpow_three_half (q : ℝ) (hq : 0 < q) : q ^ ((3:ℝ) / 2) = q * Real.sqrt q := by
  rw [Real.sqrt_eq_rpow, show (3:ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hq, Real.rpow_one]

theorem threshold_cusp_operator : ThreshCuspOp := by
  intro n q h hq
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  rw [rpow_three_half _ (by linarith)]
  set s := Real.sqrt (q:ℝ) with hs'
  have s1 : 1 ≤ s := by rw [hs']; exact Real.one_le_sqrt.mpr hq'
  have s0 : 0 < s := by linarith
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ s0]
    constructor <;> intro hx <;> nlinarith
  · intro hqn hh
    have hqn' : (q:ℝ) ≤ n := by exact_mod_cast hqn
    have hn0 : (0:ℝ) < n := by linarith
    have a3 : 0 < (n:ℝ) ^ 2 * s := by positivity
    have a1 : (n:ℝ) * q * s ≤ (n:ℝ) ^ 2 * s := by
      have : (n:ℝ) * s * q ≤ (n:ℝ) * s * n := by gcongr
      nlinarith
    refine ⟨?_, by nlinarith⟩
    rw [lt_div_iff₀ s0]
    nlinarith

theorem probability_zero : PZero := by
  intro N ep X h0 hX
  ext a b
  apply hX
  unfold q0 at h0
  rcases Nat.min_eq_zero_iff.mp h0 with h | h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    have ha := h (Finset.mem_univ a)
    have hb := h (Finset.mem_univ b)
    simp at ha hb
    rw [ha, hb]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    have ha := h (Finset.mem_univ a)
    have hb := h (Finset.mem_univ b)
    simp at ha hb
    rw [ha, hb]

theorem cube_multiplication : CubeMult := by
  intro C n f b₁ τ hC hb hτ
  have e1 : 4 / (1 / (C * n * b₁)) = 4 * (C * n * b₁) := by rw [one_div, div_inv_eq_mul]
  have s2 : Real.sqrt (n:ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  rw [e1, show 2 * n ^ 2 * f = 2 * (n ^ 2 * f) by ring, show 4 * n ^ 2 * f = 4 * (n ^ 2 * f) by ring,
    pow_mul (C * Real.sqrt n / τ ^ 2) 2, pow_mul (4 * C / τ) 4, ← mul_pow, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have e2 : (C * Real.sqrt n / τ ^ 2) ^ 2 = C ^ 2 * n / τ ^ 4 := by
    rw [div_pow, mul_pow, s2]; ring
  have e3 : (4 * C / τ) ^ 4 = 256 * C ^ 4 / τ ^ 4 := by rw [div_pow]; ring
  rw [e2, e3, mul_div_assoc', mul_div_assoc']
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hC2 : C ^ 2 ≤ 256 * C ^ 4 := by
    have : 1 ≤ C ^ 2 := by nlinarith
    nlinarith
  calc 4 * (C * n * b₁) * (C ^ 2 * n) = (4 * C * (n:ℝ) ^ 2 * b₁) * C ^ 2 := by ring
    _ ≤ (4 * C * (n:ℝ) ^ 2 * b₁) * (256 * C ^ 4) := by gcongr

theorem deepChainV_of (HD : DeepChain) : DeepChainV := by
  intro C hC
  obtain ⟨C0, hC0, H⟩ := HD C hC
  refine ⟨C0 + C, by linarith, ?_⟩
  intro n q f rd g b τ₁ τs ρ Kxx Bs D volG volK hn hq hqn hf hrd hg hb hτ hττ hD hvK hvG hρ0 hρ hK hB hvol
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hY0 : 0 < Ydat n f rd g b := by unfold Ydat; positivity
  have hb10 : 0 ≤ b1 n q f b := by unfold b1; positivity
  set Y := Ydat n f rd g b
  set Z := Y ^ (C * (n : ℝ) ^ 2 * f) with hZ
  have hZ0 : 0 < Z := Real.rpow_pos_of_pos hY0 _
  have hvol' : volG / Z / volK ≤ (C * n * rd * g) ^ (n ^ 2 * f) := by
    have e : volG / Z / volK = volG / volK / Z := by ring
    rw [e]
    calc volG / volK / Z ≤ 1 := (div_le_one hZ0).mpr hvol
      _ ≤ _ := by
        apply one_le_pow₀
        calc (1:ℝ) = 1 * 1 * 1 * 1 := by ring
          _ ≤ C * n * rd * g := by gcongr
  have key := H n q f rd g b τ₁ τs ρ Kxx Bs D (volG / Z) volK hn hq hqn hf hrd hg hb hτ hττ hD hvK
    (by positivity) hρ0 hρ hK hB hvol'
  have hτs : 0 < τs := hτ.trans hττ
  have eY : Y ^ ((C0 + C) * (n : ℝ) ^ 2 * f) = Y ^ (C0 * (n : ℝ) ^ 2 * f) * Z := by
    rw [hZ, ← Real.rpow_add hY0]; congr 1; ring
  calc volG * Kxx = Z * (volG / Z * Kxx) := by field_simp
    _ ≤ Z * (D * Y ^ (C0 * (n : ℝ) ^ 2 * f)
          * (C0 * (n : ℝ) ^ 4 * (f : ℝ) ^ 2 * g * rd * b1 n q f b) ^ (16 * q * n ^ 2 * f)
          * τs ^ (12 * n ^ 2 * f)) := by gcongr
    _ = D * (Y ^ (C0 * (n : ℝ) ^ 2 * f) * Z)
          * (C0 * (n : ℝ) ^ 4 * (f : ℝ) ^ 2 * g * rd * b1 n q f b) ^ (16 * q * n ^ 2 * f)
          * τs ^ (12 * n ^ 2 * f) := by ring
    _ ≤ _ := by
      rw [eY]
      gcongr
      linarith

theorem volume_level : VolLevel := by
  intro C n f rd g b volG volK hn hf hrd hg hb hvK hG hK
  obtain ⟨hY2, -, -, -, hgY, -⟩ := ydat_facts hn hf hrd hg hb
  have hY0 : 0 < Ydat n f rd g b := by linarith
  have e : Ydat n f rd g b ^ ((C + 2) * (n : ℝ) ^ 2 * f)
      = Ydat n f rd g b ^ (C * (n : ℝ) ^ 2 * f) * Ydat n f rd g b ^ (2 * n ^ 2 * f) := by
    rw [← Real.rpow_natCast (Ydat n f rd g b) (2 * n ^ 2 * f), ← Real.rpow_add hY0]
    congr 1; push_cast; ring
  rw [e, div_eq_mul_inv]
  have h1 : volK⁻¹ ≤ Ydat n f rd g b ^ (2 * n ^ 2 * f) :=
    hK.trans (pow_le_pow_left₀ (by linarith) hgY _)
  have h2 : 0 ≤ volK⁻¹ := by positivity
  have h3 : 0 ≤ Ydat n f rd g b ^ (C * (n : ℝ) ^ 2 * f) := (Real.rpow_pos_of_pos hY0 _).le
  calc volG * volK⁻¹ ≤ Ydat n f rd g b ^ (C * (n : ℝ) ^ 2 * f) * volK⁻¹ := by gcongr
    _ ≤ _ := by gcongr

theorem deep_region_chain_volume : DeepChainV := deepChainV_of deep_region_chain

theorem near_region_total_abs : NearTotalAbs := by
  intro c hc
  refine ⟨c / 4, c / 2, by positivity, by positivity, ?_⟩
  intro C Cg hC hCg
  have hK0 : 0 ≤ Real.log (C * (Cg + 4)) := Real.log_nonneg (by nlinarith)
  refine ⟨
    ⌈Real.exp (4 * (5 + Real.log (C * (Cg + 4))) / c)⌉₊, ?_⟩
  intro n q J a f rd g b hn hq ha haJ hJq hf hlf hb hg hgb hrd hllrd hllb
  have hn1 : Real.exp (4 * (5 + Real.log (C * (Cg + 4))) / c) ≤ n := Nat.ceil_le.mp hn
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hn1
  have hlog : 4 * (5 + Real.log (C * (Cg + 4))) / c ≤ Real.log n :=
    (Real.le_log_iff_exp_le hn0).mpr hn1
  have hlog' : 4 * (5 + Real.log (C * (Cg + 4))) ≤ c * Real.log n := by
    rw [div_le_iff₀ hc] at hlog; linarith
  have hnN : 1 ≤ n := by
    have : 0 < n := by exact_mod_cast hn0
    omega
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hnN
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hJ1 : (1:ℝ) ≤ J := by exact_mod_cast ha.trans haJ
  have hLn0 : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hY := log_ydat hnN hf hrd hg hb
  have hKe : C * (Cg + 4) = Real.exp (Real.log (C * (Cg + 4))) := (Real.exp_log (by positivity)).symm
  generalize Real.log (C * (Cg + 4)) = K at *
  have hx0 : 0 ≤ c / 4 * ((n:ℝ) * f * Real.log n) := by positivity
  have hlrd : Real.log rd ≤ Real.exp n := by
    rcases (Real.log_nonneg hrd).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · exact (Real.log_le_iff_le_exp h0).mp hllrd
  have hlb0 : 0 < Real.log b := Real.log_pos (by linarith)
  have hlb : Real.log b ≤ Real.exp (c / 4 * ((n:ℝ) * f * Real.log n)) :=
    (Real.log_le_iff_le_exp hlb0).mp (by
      have e : c / 4 * ((n:ℝ) * f * Real.log n) = c / 4 * n * f * Real.log n := by ring
      rw [e]; exact hllb)
  have hlg : Real.log g ≤ Cg * Real.log b := by
    have := Real.log_le_log (by linarith) hgb
    rwa [Real.log_rpow (by linarith)] at this
  have hne : (n:ℝ) ≤ Real.exp n := by have := Real.add_one_le_exp (n:ℝ); linarith
  have hsn : Real.sqrt (n:ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hlnn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
  have hfe : (f:ℝ) ≤ Real.exp n := by
    rw [← Real.log_le_iff_le_exp (by linarith)]; linarith
  have hq2 : (q:ℝ) ^ 2 ≤ Real.exp n := by
    have : (q:ℝ) ^ 2 ≤ n := by exact_mod_cast hq
    linarith
  have hqn1 : (q:ℝ) ≤ n := by
    have : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hq
    exact_mod_cast this
  generalize hxdef : c / 4 * ((n:ℝ) * f * Real.log n) = x4 at *
  have hE1 : Real.exp n ≤ Real.exp (n + x4) := Real.exp_le_exp.mpr (by linarith)
  have hE2 : Real.exp x4 ≤ Real.exp (n + x4) := Real.exp_le_exp.mpr (by linarith)
  have hLY : Real.log (Ydat n f rd g b) ≤ (Cg + 4) * Real.exp (n + x4) := by
    rw [hY]
    have h1 : Cg * Real.log b ≤ Cg * Real.exp (n + x4) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    linarith
  have hLY0 : 0 ≤ Real.log (Ydat n f rd g b) :=
    Real.log_nonneg (by have := (ydat_facts hnN hf hrd hg hb).1; linarith)
  generalize Real.log (Ydat n f rd g b) = LY at *
  have hbr : C * f * (q:ℝ) ^ 2 * LY ≤ Real.exp (K + 3 * n + x4) := by
    calc C * f * (q:ℝ) ^ 2 * LY ≤ C * Real.exp n * Real.exp n * ((Cg + 4) * Real.exp (n + x4)) := by
          gcongr
      _ = (C * (Cg + 4)) * (Real.exp n * Real.exp n * Real.exp (n + x4)) := by ring
      _ = _ := by
          rw [hKe, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hM0 : 0 ≤ K + 3 * n + x4 := by positivity
  have hpow : (C * f * (q:ℝ) ^ 2 * LY) ^ a ≤ Real.exp ((J:ℝ) * (K + 3 * n + x4)) := by
    calc (C * f * (q:ℝ) ^ 2 * LY) ^ a ≤ (Real.exp (K + 3 * n + x4)) ^ a := by
          apply pow_le_pow_left₀ (by positivity) hbr
      _ ≤ (Real.exp (K + 3 * n + x4)) ^ J := pow_le_pow_right₀ (Real.one_le_exp hM0) haJ
      _ = _ := (Real.exp_nat_mul _ _).symm
  have h2q : (2:ℝ) ^ q * 2 ≤ Real.exp ((q:ℝ) + 1) := by
    have h2 : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
    calc (2:ℝ) ^ q * 2 = 2 ^ (q + 1) := by ring
      _ ≤ (Real.exp 1) ^ (q + 1) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc (2:ℝ) ^ q * (2 * Real.exp (-(c * J * n * f * Real.log n))) * (C * f * (q:ℝ) ^ 2 * LY) ^ a
      = ((2:ℝ) ^ q * 2) * Real.exp (-(c * J * n * f * Real.log n)) * (C * f * (q:ℝ) ^ 2 * LY) ^ a := by
        ring
    _ ≤ Real.exp ((q:ℝ) + 1) * Real.exp (-(c * J * n * f * Real.log n))
          * Real.exp ((J:ℝ) * (K + 3 * n + x4)) := by gcongr
    _ = Real.exp ((q:ℝ) + 1 + -(c * J * n * f * Real.log n) + (J:ℝ) * (K + 3 * n + x4)) := by
        rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have e1 : c * J * n * f * Real.log n = J * (4 * x4) := by rw [← hxdef]; ring
        have e2 : c / 2 * n * f * Real.log n = 2 * x4 := by rw [← hxdef]; ring
        rw [e1, e2]
        have h5 : (5 + K) * n ≤ x4 := by
          rw [← hxdef]
          calc (5 + K) * n = (4 * (5 + K)) / 4 * (n * 1) := by ring
            _ ≤ (c * Real.log n) / 4 * (n * f) := by gcongr
            _ = _ := by ring
        have h6 : (q:ℝ) + 1 ≤ J * (n + 1) := by
          have : 1 * ((n:ℝ) + 1) ≤ J * (n + 1) := by gcongr
          linarith
        have h7 : (n:ℝ) + 1 + K + 3 * n ≤ x4 := by
          have : K * 1 ≤ K * n := by gcongr
          linarith
        have h8 : (J:ℝ) * (n + 1 + K + 3 * n) ≤ J * x4 := by gcongr
        have h9 : 1 * x4 ≤ J * x4 := by gcongr
        linarith

end Formalism.HermitianLatticeCounting.P
