import Mathlib
import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower

namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset
open Formalism.LogVandermondeBounds.StandardLattice

private lemma interlaced_lower_one_le (m : ℕ) (b w : ℕ → ℝ) (hb0 : 1 ≤ b 0) (h1 : ∀ j, j < m → b j < w j)
    (h2 : ∀ j, j + 1 < m → w j < b (j + 1)) : ∀ j, j < m → 1 ≤ b j := by
  intro j
  induction j with
  | zero => intro _; exact hb0
  | succ n ih =>
    intro hn
    have e1 := h1 n (by omega)
    have e2 := h2 n hn
    have e3 := ih (by omega)
    linarith

private lemma interlaced_sequence_monotone (m : ℕ) (b w : ℕ → ℝ) (h1 : ∀ j, j < m → b j < w j)
    (h2 : ∀ j, j + 1 < m → w j < b (j + 1)) : ∀ i j, i ≤ j → j < m → w i ≤ w j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ n hin ih =>
    intro hj
    have e1 := ih (by omega)
    have e2 := h2 n hj
    have e3 := h1 (n + 1) hj
    linarith

private lemma interlaced_log_telescoping (m : ℕ) (b w : ℕ → ℝ) (hb0 : 1 ≤ b 0) (h1 : ∀ j, j < m → b j < w j)
    (h2 : ∀ j, j + 1 < m → w j < b (j + 1)) : ∀ n, n < m →
    ∑ j ∈ range (n + 1), (Real.log (w j) - Real.log (b j)) ≤ Real.log (w n) - Real.log (b 0) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [Finset.sum_range_succ]
    have e1 := ih (by omega)
    have hb := interlaced_lower_one_le m b w hb0 h1 h2 n (by omega)
    have hwn := h1 n (by omega)
    have h2n := h2 n hn
    have : Real.log (w n) ≤ Real.log (b (n + 1)) := Real.log_le_log (by linarith) h2n.le
    linarith

private lemma interlaced_log_chain_bounds (m : ℕ) (L : ℝ) (b w : ℕ → ℝ) (hm : 1 ≤ m) (hb0 : 1 ≤ b 0)
    (h1 : ∀ j, j < m → b j < w j) (h2 : ∀ j, j + 1 < m → w j < b (j + 1))
    (htop : w (m - 1) ≤ 2 * Real.exp L) :
    (∀ j, j < m → 1 ≤ b j ∧ 1 < w j ∧ Real.log (b j) ≤ L + Real.log 2) ∧
    0 ≤ ∑ j ∈ range m, (Real.log (w j) - Real.log (b j)) ∧
    ∑ j ∈ range m, (Real.log (w j) - Real.log (b j)) ≤ L + Real.log 2 := by
  have hlog : Real.log (2 * Real.exp L) = L + Real.log 2 := by
    rw [Real.log_mul (by norm_num) (Real.exp_pos L).ne', Real.log_exp]; ring
  have hbg := interlaced_lower_one_le m b w hb0 h1 h2
  have hwle := interlaced_sequence_monotone m b w h1 h2
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have e1 := hbg j hj
    have e2 := h1 j hj
    have e3 := hwle j (m - 1) (by omega) (by omega)
    refine ⟨e1, by linarith, ?_⟩
    rw [← hlog]
    exact Real.log_le_log (by linarith) (by linarith)
  · apply Finset.sum_nonneg
    intro j hj
    rw [Finset.mem_range] at hj
    have e1 := hbg j hj
    have e2 := h1 j hj
    have : Real.log (b j) ≤ Real.log (w j) := Real.log_le_log (by linarith) e2.le
    linarith
  · have e := interlaced_log_telescoping m b w hb0 h1 h2 (m - 1) (by omega)
    rw [show m - 1 + 1 = m by omega] at e
    have hwm := h1 (m - 1) (by omega)
    have hbm := hbg (m - 1) (by omega)
    have e4 : Real.log (w (m - 1)) ≤ L + Real.log 2 := by
      rw [← hlog]; exact Real.log_le_log (by linarith) htop
    have e5 : 0 ≤ Real.log (b 0) := Real.log_nonneg hb0
    linarith

private lemma log_volume_ratio_bounds (L vE : ℝ) (hv : Real.pi ≤ vE) (hL : Real.log vE ≤ L) :
    0 ≤ Real.log (vE / Real.pi) ∧ Real.log (vE / Real.pi) ≤ L ∧ 0 ≤ L := by
  have hpi := Real.pi_pos
  have hv0 : 0 < vE := by linarith
  have h1 : 1 ≤ vE / Real.pi := by rw [le_div_iff₀ hpi]; linarith
  have h2 : 0 ≤ Real.log (vE / Real.pi) := Real.log_nonneg h1
  have h3 : Real.log (vE / Real.pi) = Real.log vE - Real.log Real.pi :=
    Real.log_div hv0.ne' hpi.ne'
  have h4 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h5 : Real.log Real.pi ≤ Real.log vE := Real.log_le_log hpi hv
  exact ⟨h2, by linarith, by linarith⟩

theorem bracket_bound : BracketSumBound := by
  intro k m L vE G b w hk hm hv hL hG hb0 h1 h2 htop
  obtain ⟨hl0, hlL, hL0⟩ := log_volume_ratio_bounds L vE hv hL
  obtain ⟨hj, hs0, hsL⟩ := interlaced_log_chain_bounds m L b w hm hb0 h1 h2 htop
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hkpos : (0 : ℝ) < k := by linarith
  have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
  have hc : 0 ≤ (m : ℝ) * (m - 1) / (2 * k) := by
    apply div_nonneg
    · nlinarith
    · linarith
  have hlG : 0 ≤ Real.log G := Real.log_nonneg hG
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hc hl0]
  · nlinarith [mul_nonneg hc hlG]
  · have hSb : ∑ j ∈ range m, Real.log (b j) ≤ (m : ℝ) * (L + Real.log 2) := by
      have := Finset.sum_le_sum (s := range m) (f := fun j => Real.log (b j))
        (g := fun _ => L + Real.log 2) (fun j hj' => (hj j (Finset.mem_range.mp hj')).2.2)
      simp at this
      linarith
    rw [Finset.sum_sub_distrib] at hsL
    have hdiv : (∑ j ∈ range m, Real.log (b j)) / k ≤ (m : ℝ) * (L + Real.log 2) / k := by
      gcongr
    have hrw : ((k : ℝ) - 1) / k * ∑ j ∈ range m, Real.log (b j) =
        ∑ j ∈ range m, Real.log (b j) - (∑ j ∈ range m, Real.log (b j)) / k := by
      field_simp
    rw [hrw]
    linarith

theorem initial_sum_comparison : InterlacedProductComparison := by
  intro L vE aeff A m b w hm hv hL hb0 h1 h2 htop ha hA
  dsimp only
  rw [inv_div]
  obtain ⟨hl0, hlL, hL0⟩ := log_volume_ratio_bounds L vE hv hL
  obtain ⟨hj, hs0, hsL⟩ := interlaced_log_chain_bounds m L b w hm hb0 h1 h2 htop
  have hpi := Real.pi_pos
  have hv0 : 0 < vE := by linarith
  have hbpos : ∀ j ∈ range m, 0 < b j := fun j hj' => by
    have := (hj j (Finset.mem_range.mp hj')).1
    linarith
  have hwpos : ∀ j ∈ range m, 0 < w j := fun j hj' => by
    have := (hj j (Finset.mem_range.mp hj')).2.1
    linarith
  have hB : 0 < ∏ j ∈ range m, b j := Finset.prod_pos hbpos
  have hW : 0 < ∏ j ∈ range m, w j := Finset.prod_pos hwpos
  have hc : 0 < vE / Real.pi := div_pos hv0 hpi
  have eL : ∏ j ∈ range m, w j * vE / Real.pi = (∏ j ∈ range m, w j) * (vE / Real.pi) ^ m := by
    simp_rw [mul_div_assoc]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hpow : (vE / Real.pi) ^ m = (vE / Real.pi) ^ (m - 1) * (vE / Real.pi) := by
    rw [← pow_succ]
    congr 1
    omega
  have e1 : ∏ j ∈ range m, w j * vE / Real.pi =
      ((vE / Real.pi) ^ (m - 1) * (∏ j ∈ range m, b j) / aeff) *
        (vE / Real.pi * aeff * ∏ j ∈ range m, w j / b j) := by
    rw [eL, Finset.prod_div_distrib, hpow]
    have hB0 := hB.ne'
    have ha0 := ha.ne'
    field_simp
  refine ⟨e1, ?_⟩
  have hX : 0 < (vE / Real.pi) ^ (m - 1) * (∏ j ∈ range m, b j) / aeff := by positivity
  have hQ : 0 < ∏ j ∈ range m, w j / b j :=
    Finset.prod_pos (fun j hj' => div_pos (hwpos j hj') (hbpos j hj'))
  have hY : 0 < vE / Real.pi * aeff * ∏ j ∈ range m, w j / b j := by positivity
  rw [e1, Real.log_mul hX.ne' hY.ne', add_sub_cancel_left,
    Real.log_mul (by positivity) hQ.ne', Real.log_mul hc.ne' ha.ne']
  have hsum : Real.log (∏ j ∈ range m, w j / b j) =
      ∑ j ∈ range m, (Real.log (w j) - Real.log (b j)) := by
    rw [Real.log_prod (fun j hj' => (div_pos (hwpos j hj') (hbpos j hj')).ne')]
    apply Finset.sum_congr rfl
    intro j hj'
    exact Real.log_div (hwpos j hj').ne' (hbpos j hj').ne'
  rw [hsum]
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abs_le]
  constructor <;> linarith

theorem volume_parameter_bounds : VolumeParameterBounds := by
  intro e q d he hq hd
  dsimp only
  have he' : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hd' : (7 : ℝ) ≤ d := by exact_mod_cast hd
  have hpe : (2 : ℝ) ^ (-(e : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hpe0 : 0 < (2 : ℝ) ^ (-(e : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hx : (2 : ℝ) ≤ (e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ)) := by linarith
  have h4x : (4 : ℝ) ≤ (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) := by
    have h22 : (2 : ℝ) ^ (2 : ℝ) = 4 := by rw [Real.rpow_two]; norm_num
    rw [← h22]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hx
  have hqd : (21 : ℝ) ≤ q * d := by nlinarith
  have hs : (4 : ℝ) ≤ Real.sqrt (q * d) := by
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [← h16]
    exact Real.sqrt_le_sqrt (by linarith)
  constructor
  · have hprod : (16 : ℝ) ≤ (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt (q * d) := by
      nlinarith
    linarith [Real.pi_le_four]
  · have hs0 : 0 < Real.sqrt (q * d) := by linarith
    have h2x0 : 0 < (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) := by positivity
    rw [Real.log_div (by positivity) (by norm_num), Real.log_mul h2x0.ne' hs0.ne',
      Real.log_rpow (by norm_num), Real.log_sqrt (by positivity),
      Real.log_mul (two_ne_zero : (2 : ℝ) ≠ 0) (pow_ne_zero e (two_ne_zero : (2 : ℝ) ≠ 0)),
      Real.log_pow]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [mul_pos hpe0 hl2]

theorem volume_parameter_le_log : LogVolumeLeParameter := by
  intro ε C₀ A hε hC hA
  have hε0 := hε.ne'
  set K := Real.log 2 + 5 * C₀ / ε + A / 2 + 25 * A / (2 * ε ^ 2) with hK
  have hK0 : 0 ≤ K := by
    have a1 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have a2 : 0 ≤ 5 * C₀ / ε := by positivity
    have a3 : 0 ≤ A / 2 := by positivity
    have a4 : 0 ≤ 25 * A / (2 * ε ^ 2) := by positivity
    rw [hK]
    linarith
  refine ⟨max 1 ((K + 1) ^ (5 / ε)), ?_⟩
  intro x hx n q d hn hq hd hnx hqx hdx
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hy1 : K + 1 ≤ x ^ (ε / 5) := by
    have h1 : (K + 1) ^ (5 / ε) ≤ x := le_trans (le_max_right _ _) hx
    have h2 : ((K + 1) ^ (5 / ε)) ^ (ε / 5) ≤ x ^ (ε / 5) :=
      Real.rpow_le_rpow (by positivity) h1 (by positivity)
    have h3 : (5 / ε) * (ε / 5) = 1 := by
      first | (field_simp; done) | (field_simp; ring)
    rwa [← Real.rpow_mul (by positivity), h3, Real.rpow_one] at h2
  have hxe : x ^ ε = (x ^ (ε / 5)) ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    push_cast
    ring
  have hlogx : Real.log x ≤ 5 / ε * x ^ (ε / 5) := by
    have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 (ε / 5))
    rw [Real.log_rpow hx0] at h1
    have h2 : ε / 5 * Real.log x ≤ x ^ (ε / 5) := by linarith
    have h3 : Real.log x = 5 / ε * (ε / 5 * Real.log x) := by
      first | (field_simp; done) | (field_simp; ring)
    rw [h3]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hn0 : 0 < n := by linarith
  have hq0 : 0 < q := by linarith
  have hd0 : 0 < d := by linarith
  have h2n : Real.log (2 * n) ≤ Real.log 2 + C₀ * Real.log x := by
    rw [Real.log_mul (by norm_num) hn0.ne']
    have h := Real.log_le_log hn0 hnx
    rw [Real.log_rpow hx0] at h
    linarith
  have hqd : Real.log (q * d) = Real.log q + Real.log d := Real.log_mul hq0.ne' hd0.ne'
  have hy0 : 1 ≤ x ^ (ε / 5) := by linarith
  have hy3 : x ^ (ε / 5) ≤ (x ^ (ε / 5)) ^ 3 := by
    first | exact le_self_pow₀ hy0 (by norm_num) | exact le_self_pow hy0 (by norm_num)
  have hy2 : x ^ (ε / 5) ≤ (x ^ (ε / 5)) ^ 2 := by
    first | exact le_self_pow₀ hy0 (by norm_num) | exact le_self_pow hy0 (by norm_num)
  have hy3' : 1 ≤ (x ^ (ε / 5)) ^ 3 := le_trans hy0 hy3
  have hsq : (Real.log x) ^ 2 ≤ (5 / ε * x ^ (ε / 5)) ^ 2 := pow_le_pow_left₀ hlog0 hlogx 2
  have t1 : C₀ * Real.log x ≤ 5 * C₀ / ε * x ^ (ε / 5) := by
    have h := mul_le_mul_of_nonneg_left hlogx hC
    calc C₀ * Real.log x ≤ C₀ * (5 / ε * x ^ (ε / 5)) := h
      _ = 5 * C₀ / ε * x ^ (ε / 5) := by ring
  have t2 : A * x ^ (ε / 5) * (Real.log x) ^ 2 ≤ 25 * A / ε ^ 2 * (x ^ (ε / 5)) ^ 3 := by
    have hAy : 0 ≤ A * x ^ (ε / 5) := by positivity
    calc A * x ^ (ε / 5) * (Real.log x) ^ 2 ≤ A * x ^ (ε / 5) * (5 / ε * x ^ (ε / 5)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hAy
      _ = 25 * A / ε ^ 2 * (x ^ (ε / 5)) ^ 3 := by
          first | (field_simp; done) | (field_simp; ring)
  have c1 : 5 * C₀ / ε * x ^ (ε / 5) ≤ 5 * C₀ / ε * (x ^ (ε / 5)) ^ 3 :=
    mul_le_mul_of_nonneg_left hy3 (by positivity)
  have c2 : A * x ^ (ε / 5) ≤ A * (x ^ (ε / 5)) ^ 3 := mul_le_mul_of_nonneg_left hy3 hA
  have c3 : Real.log 2 ≤ Real.log 2 * (x ^ (ε / 5)) ^ 3 :=
    le_mul_of_one_le_right (Real.log_nonneg (by norm_num)) hy3'
  have main : Real.log (2 * n) + Real.log (q * d) / 2 ≤ K * (x ^ (ε / 5)) ^ 3 := by
    rw [hqd, hK]
    have e : (Real.log 2 + 5 * C₀ / ε + A / 2 + 25 * A / (2 * ε ^ 2)) * (x ^ (ε / 5)) ^ 3 =
        Real.log 2 * (x ^ (ε / 5)) ^ 3 + 5 * C₀ / ε * (x ^ (ε / 5)) ^ 3 +
          (A * (x ^ (ε / 5)) ^ 3) / 2 + (25 * A / ε ^ 2 * (x ^ (ε / 5)) ^ 3) / 2 := by
      first | (field_simp; done) | (field_simp; ring) | ring
    rw [e]
    linarith
  have hKy : K ≤ (x ^ (ε / 5)) ^ 2 := by linarith
  rw [hxe]
  calc Real.log (2 * n) + Real.log (q * d) / 2 ≤ K * (x ^ (ε / 5)) ^ 3 := main
    _ ≤ (x ^ (ε / 5)) ^ 2 * (x ^ (ε / 5)) ^ 3 :=
        mul_le_mul_of_nonneg_right hKy (by positivity)
    _ = (x ^ (ε / 5)) ^ 5 := by ring

private lemma triangular_number_succ (j : ℕ) : (j + 1 + 1) * (j + 1) / 2 = (j + 1) * j / 2 + (j + 1) := by
  have h : (j + 1 + 1) * (j + 1) = (j + 1) * j + (j + 1) * 2 := by ring
  rw [h, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]

private lemma factorial_product_rearrangement (f k j : ℕ) (a s : ℝ) (hs : s ≠ 0) (Lval : ℕ → ℝ) :
    (∏ M ∈ Ico (k + 1) (k + j + 1), ((((M - 1).factorial : ℕ) : ℝ) * a ^ M) ^ f / s * Lval M)
        * (∏ i ∈ range k, ((i.factorial : ℕ) : ℝ)) ^ f * s ^ j
      = (∏ M ∈ Ico (k + 1) (k + j + 1), Lval M) * (a ^ (j * k + (j + 1) * j / 2)) ^ f
        * (∏ i ∈ range (k + j), ((i.factorial : ℕ) : ℝ)) ^ f := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hT : k + j + 1 - 1 = k + j := by omega
    rw [show k + (j + 1) + 1 = k + j + 1 + 1 by omega,
      Finset.prod_Ico_succ_top (by omega : k + 1 ≤ k + j + 1),
      Finset.prod_Ico_succ_top (by omega : k + 1 ≤ k + j + 1),
      show k + (j + 1) = k + j + 1 by omega, Finset.prod_range_succ, hT]
    have e1 : (j + 1) * k + (j + 1 + 1) * (j + 1) / 2 = (j * k + (j + 1) * j / 2) + (k + j + 1) := by
      rw [triangular_number_succ]
      ring
    rw [e1]
    have hsx : ∀ X Y : ℝ, X / s * Y * s = X * Y := fun X Y => by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hs]
    calc _ = (∏ M ∈ Ico (k + 1) (k + j + 1), ((((M - 1).factorial : ℕ) : ℝ) * a ^ M) ^ f / s * Lval M)
            * (∏ i ∈ range k, ((i.factorial : ℕ) : ℝ)) ^ f * s ^ j
            * (((((k + j).factorial : ℕ) : ℝ) * a ^ (k + j + 1)) ^ f / s * Lval (k + j + 1) * s) := by
          ring
      _ = (∏ M ∈ Ico (k + 1) (k + j + 1), Lval M) * (a ^ (j * k + (j + 1) * j / 2)) ^ f
            * (∏ i ∈ range (k + j), ((i.factorial : ℕ) : ℝ)) ^ f
            * (((((k + j).factorial : ℕ) : ℝ) * a ^ (k + j + 1)) ^ f / s * Lval (k + j + 1) * s) := by
          rw [ih]
      _ = _ := by
          rw [hsx]
          ring

theorem initial_sum_identity : InitialSumIdentity := by
  intro f m k vE g₁ g₂ u Dstar dstar massk massr Isig Ipi Lval dsig hm hk hv hg1 hg2 hmk hIpi
    hvand hmass hD hd
  rw [inv_div]
  have hpi := Real.pi_pos
  have hc : 0 < vE / Real.pi := div_pos hv hpi
  have h2v : 0 < 2 * vE := by positivity
  set S := Real.sqrt ((2 * vE) ^ f) with hSdef
  have hS : 0 < S := Real.sqrt_pos.mpr (by positivity)
  have hbound : k - 1 + m = k + (m - 1) := by omega
  have hexp : (m - 1) * k + m * (m - 1) / 2 = (m - 1) * k + (m - 1 + 1) * (m - 1) / 2 := by
    rw [Nat.sub_add_cancel hm]
  have key := factorial_product_rearrangement f k (m - 1) (vE / Real.pi) S hS.ne' Lval
  rw [← hbound, ← hexp] at key
  set P := ∏ M ∈ Ico (k + 1) (k - 1 + m + 1),
    ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / S * Lval M with hP
  have hV : 0 < ∏ ρ ∈ range f, vandN (u ρ) k :=
    Finset.prod_pos (fun ρ hρ => hvand ρ (Finset.mem_range.mp hρ))
  have hFk : 0 < ∏ i ∈ range k, ((i.factorial : ℕ) : ℝ) :=
    Finset.prod_pos (fun i _ => by positivity)
  have hdim : ∏ ρ ∈ range f, dimVN (u ρ) k =
      (∏ ρ ∈ range f, vandN (u ρ) k) / (∏ i ∈ range k, ((i.factorial : ℕ) : ℝ)) ^ f := by
    simp only [dimVN, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hS' : S = (2 * vE) ^ ((f : ℝ) / 2) := by
    rw [hSdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h2v.le]
    congr 1
    ring
  have hT : ((2 * vE) ^ (-(((m : ℝ) - 1) / 2))) ^ f * S ^ (m - 1) = 1 := by
    rw [hS', ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul h2v.le,
      ← Real.rpow_mul h2v.le, ← Real.rpow_add h2v]
    convert Real.rpow_zero (2 * vE) using 2
    rw [Nat.cast_sub hm]
    push_cast
    ring
  have hT' : ((2 * vE) ^ (-(((m : ℝ) - 1) / 2))) ^ f = (S ^ (m - 1))⁻¹ :=
    eq_inv_of_mul_eq_one_left hT
  have hP' : P = (∏ M ∈ Ico (k + 1) (k - 1 + m + 1), Lval M) *
      ((vE / Real.pi) ^ ((m - 1) * k + m * (m - 1) / 2)) ^ f *
      (∏ i ∈ range (k - 1 + m), ((i.factorial : ℕ) : ℝ)) ^ f /
      ((∏ i ∈ range k, ((i.factorial : ℕ) : ℝ)) ^ f * S ^ (m - 1)) := by
    rw [eq_div_iff (by positivity), ← key]
    ring
  rw [hD, hd, hdim, hmass, hP']
  simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  rw [hT', pow_mul' (g₁ * g₂) f (k * m + m * (m - 1) / 2)]
  have h1 := hmk.ne'
  have h2 := hIpi.ne'
  have h3 := hV.ne'
  have h4 := hFk.ne'
  have h5 := hS.ne'
  have h6 : g₁ * g₂ ≠ 0 := (mul_pos hg1 hg2).ne'
  have h7 := hc.ne'
  field_simp

end Formalism.HermitianLattices.GenusMassVolumes
