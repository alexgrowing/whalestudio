import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountUpper
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefSmallApprox
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountUpperCurve
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUpperNormalisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

theorem NefCountUpper.proof (hApx : NefSmallApprox.Statement) (hCurve : NefCountUpperCurve.Statement)
    (h7 : G7.Statement) (hPack : PackingStatement) : NefCountUpper.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen hht ε hε
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · filter_upwards [hCurve K ι Ω y A P0 II hII har hb hP0 hs hc hnef hgen hht ε hε] with n hn
    simpa using hn
  have : CharZero Ω := UpperNormalisation.charZero_of_isArithVar har
  set F : ℝ := ((D + 1).factorial : ℝ) with hF
  have hFpos : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _
  set IA := II K ι (mCoordIdeal y) (D + 1) (fun _ => A) with hIA
  obtain ⟨q, B, P1, hq, hsg, hBc, htop, hev⟩ :=
    hApx K ι Ω y D A P0 II hD hII har hb hP0 hs hc hnef hgen hht (ε / 4) (by linarith)
  set IB := II K ι (mCoordIdeal y) (D + 1) (fun _ => B) with hIB
  set T : ℝ := IA + ε / 2 with hT
  have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ (D + 1) := one_le_pow₀ (by exact_mod_cast hq)
  have hBT : IB + ε / 4 ≤ (q : ℝ) ^ (D + 1) * T := by
    have : ε / 4 ≤ (q : ℝ) ^ (D + 1) * (ε / 4) := le_mul_of_one_le_left (by linarith) hq1
    rw [hT]; nlinarith
  obtain ⟨hfin, Cp, hCp⟩ := hPack K ι Ω y D B (chartLat y B.a) har hb hsg.semipos.1
    (fun τ => Mono.chartLat_le_nm y B.a τ)
  have hG7 := h7 K ι Ω y D B P1 II hD hII har hb hsg hBc

  set v : ℕ → ℝ := fun N => smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLat y B.a) N /
    ((N : ℝ) ^ (D + 1) / F) with hv
  have hv_bdd : ∀ N, v N ≤ |Cp| * F * 2 ^ (D + 1) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [hv, Nat.cast_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow, zero_div, div_zero]
      positivity
    · have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hNpos : (0 : ℝ) < (N : ℝ) ^ (D + 1) / F := by positivity
      simp only [hv]
      rw [div_le_iff₀ hNpos]
      have h1 := (hCp N).trans (mul_le_mul_of_nonneg_right (le_abs_self Cp) (by positivity))
      have h2 : ((N : ℝ) + 1) ^ (D + 1) ≤ (2 * N) ^ (D + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
      calc _ ≤ |Cp| * ((N : ℝ) + 1) ^ (D + 1) := h1
        _ ≤ |Cp| * (2 * N) ^ (D + 1) := mul_le_mul_of_nonneg_left h2 (abs_nonneg Cp)
        _ = |Cp| * F * 2 ^ (D + 1) * ((N : ℝ) ^ (D + 1) / F) := by rw [mul_pow]; field_simp
  have hev1 : ∀ᶠ N in atTop, v N < IB + ε / 4 :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hG7 (by linarith)) (isBoundedUnder_of ⟨_, hv_bdd⟩)
  have hNq : Tendsto (fun n : ℕ => n / q + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ _) (Nat.tendsto_div_const_atTop (Nat.one_le_iff_ne_zero.mp hq))
  have hlim : Tendsto (fun n : ℕ => T * (1 + (q : ℝ) / n) ^ (D + 1)) atTop (𝓝 T) := by
    have h0 : Tendsto (fun n : ℕ => (q : ℝ) / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h0).pow (D + 1) |>.const_mul T
  filter_upwards [hNq.eventually hev1, hlim.eventually (gt_mem_nhds (show T < IA + ε by linarith)), hev,
    eventually_ge_atTop 1] with n h2 h3 ⟨t, ht0, hts⟩ hn1
  set N := n / q + 1 with hN
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hNpos : (0 : ℝ) < (N : ℝ) ^ (D + 1) / F := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.succ_pos _
    positivity

  have hcmp : smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLat y B.a) N :=
    Mono.smallSectionCount_le_of_injOn (Q := fun m => IsSmallH (mCoordIdeal y) y B (m / q + 1))
      (La' := fun m => chartLat y B.a (m / q + 1)) (fun s => s * t)
      (fun s _ u _ hsu => mul_right_cancel₀ ht0 hsu) (fun s hs hsm => hts s hs hsm) (hfin N)
  have hcount : smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLat y B.a) N ≤
      (IB + ε / 4) * ((N : ℝ) ^ (D + 1) / F) := by
    have := h2
    simp only [hv] at this
    rw [div_lt_iff₀ hNpos] at this
    exact this.le

  have hlo : (n : ℝ) ≤ q * N := by
    have := Nat.lt_mul_div_succ n (show 0 < q by omega)
    exact_mod_cast this.le
  have hhi : (q : ℝ) * N ≤ n + q := by
    have : q * (n / q) ≤ n := Nat.mul_div_le n q
    have : q * N ≤ n + q := by rw [hN, mul_add, mul_one]; omega
    exact_mod_cast this
  set X : ℝ := ((q : ℝ) * N) ^ (D + 1) with hX
  have hX1 : (n : ℝ) ^ (D + 1) ≤ X := pow_le_pow_left₀ hnpos.le hlo _
  have hX2 : X ≤ ((n : ℝ) + q) ^ (D + 1) := pow_le_pow_left₀ (by positivity) hhi _
  have hratio : ((n : ℝ) + q) ^ (D + 1) = (1 + (q : ℝ) / n) ^ (D + 1) * (n : ℝ) ^ (D + 1) := by
    rw [← mul_pow]; congr 1; field_simp
  have hTX : T * X ≤ (IA + ε) * (n : ℝ) ^ (D + 1) := by
    rcases le_or_gt 0 T with hT0 | hT0
    · calc T * X ≤ T * ((n : ℝ) + q) ^ (D + 1) := mul_le_mul_of_nonneg_left hX2 hT0
        _ = (T * (1 + (q : ℝ) / n) ^ (D + 1)) * (n : ℝ) ^ (D + 1) := by rw [hratio]; ring
        _ ≤ (IA + ε) * (n : ℝ) ^ (D + 1) := mul_le_mul_of_nonneg_right h3.le (by positivity)
    · calc T * X ≤ T * (n : ℝ) ^ (D + 1) := mul_le_mul_of_nonpos_left hX1 hT0.le
        _ ≤ (IA + ε) * (n : ℝ) ^ (D + 1) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  calc smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n
      ≤ (IB + ε / 4) * ((N : ℝ) ^ (D + 1) / F) := hcmp.trans hcount
    _ ≤ ((q : ℝ) ^ (D + 1) * T) * ((N : ℝ) ^ (D + 1) / F) := mul_le_mul_of_nonneg_right hBT hNpos.le
    _ = (T * X) / F := by rw [hX, mul_pow]; ring
    _ ≤ ((IA + ε) * (n : ℝ) ^ (D + 1)) / F := div_le_div_of_nonneg_right hTX hFpos.le
    _ = (IA + ε) * ((n : ℝ) ^ (D + 1) / F) := by ring

end

end GroundTheory.Heights₂.Heights.Targets
