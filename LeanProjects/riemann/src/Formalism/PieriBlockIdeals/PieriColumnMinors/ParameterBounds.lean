import Formalism.PieriBlockIdeals.MertensReciprocalElementary
import Formalism.PieriBlockIdeals.PieriColumnMinors.SharperSizeNeedsMleKFalse
import Formalism.PieriBlockIdeals.PieriColumnMinors.LocalComponentGL
import Formalism.PieriBlockIdeals.PieriColumnMinors.LogarithmEquivalence
import Formalism.RankGapBounds.RankGapProofs.CardLargePrimeFactorsLeOneHolds

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent.LogSmallConstantBounds

open Classical

private theorem log_two_le_seven_tenths : Real.log 2 ≤ 7 / 10 := by
  have h := Real.log_two_lt_d9
  have d : (0.6931471808 : ℝ) = 6931471808 / 10000000000 := by norm_num
  rw [d] at h
  linarith

private theorem log_three_le_eleven_tenths : Real.log 3 ≤ 11 / 10 := by
  have h1 : Real.log (243 / 256 : ℝ) ≤ 243 / 256 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h2 : Real.log (243 / 256 : ℝ) = 5 * Real.log 3 - 8 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (243 : ℝ) = 3 ^ 5 by norm_num,
      show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h3 := Real.log_two_lt_d9
  have d : (0.6931471808 : ℝ) = 6931471808 / 10000000000 := by norm_num
  rw [d] at h3
  linarith

private theorem log_six_le' : Real.log 6 ≤ 9 / 5 := by
  have e : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h1 := log_two_le_seven_tenths
  have h2 := log_three_le_eleven_tenths
  linarith

def lstarDenom (P : Par) : ℝ :=
  (P.n : ℝ) * (P.t : ℝ) ^ 2 * (P.N + (P.t : ℝ)) * P.L ^ 2
      + (P.k : ℝ) * (P.n : ℝ) ^ 2 * (P.S + (P.t : ℝ) + P.L)

theorem lstar_eq_div (P : Par) : P.lstar = (P.m : ℝ) * P.b / lstarDenom P := rfl

theorem b_pos' (P : Par) : 0 < P.b := Real.exp_pos _

theorem log_b' (P : Par) : Real.log P.b = P.L := Real.log_exp _

structure NatBounds (P : Par) : Prop where
  m1 : (1 : ℝ) ≤ P.m
  n1 : (1 : ℝ) ≤ P.n
  f1 : (1 : ℝ) ≤ P.f
  k1 : (1 : ℝ) ≤ P.k
  mlek : (P.m : ℝ) ≤ P.k
  kt : (P.k : ℝ) + P.m + 4 ≤ P.t
  mt : 3 * (P.m : ℝ) < P.t
  t6 : (6 : ℝ) ≤ P.t
  nr : (P.Nr : ℝ) + 1 = P.k + P.m + P.t
  nr2 : (P.Nr : ℝ) ≤ 2 * P.t - 5

theorem natBounds {P : Par} (H : P.Hyp) : NatBounds P := by
  have hm : (1 : ℝ) ≤ P.m := by exact_mod_cast H.m_pos
  have hk : (1 : ℝ) ≤ P.k := by exact_mod_cast le_trans H.m_pos H.m_le
  have ht : (P.k : ℝ) + P.m + 4 ≤ P.t := by exact_mod_cast H.t_ge
  have hN : (P.Nr : ℝ) + 1 = P.k + P.m + P.t := by exact_mod_cast H.Nr_eq
  exact ⟨hm, by exact_mod_cast H.n_pos, by exact_mod_cast H.f_pos, hk,
    by exact_mod_cast H.m_le, ht, by exact_mod_cast H.t_gt, by linarith, hN, by linarith⟩

theorem le_lstarDenom {P : Par} (H : P.Hyp) (G : P.Large) :
    (P.t : ℝ) ^ 3 * P.L ^ 2 ≤ lstarDenom P := by
  have nb := natBounds H
  have hS := H.S_nonneg
  have hL := G.L_ge
  have ht0 : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  have hN : 0 ≤ P.N := by unfold Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.N; positivity
  have h1 : (P.t : ℝ) ≤ P.n * (P.N + P.t) := by
    nlinarith [mul_nonneg (sub_nonneg.2 nb.n1) (add_nonneg hN ht0)]
  have h2 : 0 ≤ (P.k : ℝ) * (P.n : ℝ) ^ 2 * (P.S + P.t + P.L) :=
    mul_nonneg (by positivity) (by linarith)
  have h4 : 0 ≤ (P.t : ℝ) ^ 2 * P.L ^ 2 := by positivity
  have h3 : (P.t : ℝ) ^ 3 * P.L ^ 2 ≤ P.n * P.t ^ 2 * (P.N + P.t) * P.L ^ 2 := by
    calc (P.t : ℝ) ^ 3 * P.L ^ 2 = ((P.t : ℝ) ^ 2 * P.L ^ 2) * P.t := by ring
      _ ≤ ((P.t : ℝ) ^ 2 * P.L ^ 2) * (P.n * (P.N + P.t)) := mul_le_mul_of_nonneg_left h1 h4
      _ = P.n * P.t ^ 2 * (P.N + P.t) * P.L ^ 2 := by ring
  unfold lstarDenom
  linarith

theorem lstarDenom_pos {P : Par} (H : P.Hyp) (G : P.Large) : 0 < lstarDenom P := by
  have nb := natBounds H
  have hL := G.L_ge
  have : (0 : ℝ) < (P.t : ℝ) ^ 3 * P.L ^ 2 :=
    mul_pos (pow_pos (by linarith [nb.t6]) 3) (pow_pos (by linarith) 2)
  exact lt_of_lt_of_le this (le_lstarDenom H G)

theorem lstar_pos {P : Par} (H : P.Hyp) (G : P.Large) : 0 < P.lstar := by
  have nb := natBounds H
  rw [lstar_eq_div]
  exact div_pos (mul_pos (by linarith [nb.m1]) (b_pos' P)) (lstarDenom_pos H G)

theorem b_div_lstar_pos {P : Par} (H : P.Hyp) (G : P.Large) : 0 < P.b / P.lstar :=
  div_pos (b_pos' P) (lstar_pos H G)

theorem two_mul_lstar_le_b {P : Par} (H : P.Hyp) (G : P.Large) : 2 * P.lstar ≤ P.b := by
  have nb := natBounds H
  have hL := G.L_ge
  have hb := b_pos' P
  have hD := lstarDenom_pos H G
  have hle := le_lstarDenom H G
  have ht6 := nb.t6
  have ht2 : (36 : ℝ) ≤ (P.t : ℝ) ^ 2 := by nlinarith
  have hL2 : (16 : ℝ) ≤ P.L ^ 2 := by nlinarith
  have h36' := mul_le_mul ht2 hL2 (by norm_num) (by positivity)
  have h36 : (1 : ℝ) ≤ (P.t : ℝ) ^ 2 * P.L ^ 2 := by linarith
  have htt : (P.t : ℝ) ≤ (P.t : ℝ) ^ 3 * P.L ^ 2 := by
    have := mul_le_mul_of_nonneg_left h36 (by linarith : (0 : ℝ) ≤ P.t)
    nlinarith
  have hm : 2 * (P.m : ℝ) ≤ lstarDenom P := by linarith [nb.mt, nb.m1]
  rw [lstar_eq_div, mul_div_assoc', div_le_iff₀ hD]
  nlinarith

theorem eta_nonneg' {P : Par} (H : P.Hyp) : 0 ≤ P.η := le_trans (Nat.cast_nonneg _) H.t_le

private theorem lstar_bounds_of_large {P : Par} (H : P.Hyp) (G : P.Large) :
    P.S + P.η < P.lstar ∧ 2 * P.η + P.t + 7 < P.lstar ∧ 2 * P.lstar ≤ P.b ∧ 0 < P.b / P.lstar := by
  have h1 := H.sum_lt
  have h2 := H.win_lt
  have hb' := H.b'_pos
  have hbl := b_div_lstar_pos H G
  have e : 8 * P.b / P.lstar = 8 * (P.b / P.lstar) := by ring
  exact ⟨by linarith, by linarith, two_mul_lstar_le_b H G, hbl⟩

theorem paramsBasic_holds : Elem0 := by
  intro P H G
  have hNr := H.Nr_eq
  have htg := H.t_ge
  obtain ⟨a1, a2, a3, a4⟩ := lstar_bounds_of_large H G
  have hη := eta_nonneg' H
  have htη := H.t_le
  refine ⟨by omega, a3, ?_⟩
  unfold Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.h
  linarith

theorem b_add_seven_le_h {P : Par} (H : P.Hyp) : P.b + 7 ≤ P.h := by
  have nb := natBounds H
  have := H.t_le
  have := H.S_nonneg
  unfold Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.h
  linarith [nb.t6]

theorem log_three_mul_h_bounds {P : Par} (H : P.Hyp) (G : P.Large) :
    P.L ≤ Real.log (3 * P.h) ∧ Real.log (3 * P.h) ≤ P.L + Real.log 6 := by
  have hb := b_pos' P
  have hh : P.h ≤ 2 * P.b := (paramsBasic_holds P H G).2.2
  have hh2 := b_add_seven_le_h H
  constructor
  · rw [← log_b' P]
    exact Real.log_le_log hb (by linarith)
  · calc Real.log (3 * P.h) ≤ Real.log (6 * P.b) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 6 + P.L := by rw [Real.log_mul (by norm_num) hb.ne', log_b']
      _ = P.L + Real.log 6 := by ring

theorem log_three_mul_h_pos_le {P : Par} (H : P.Hyp) (G : P.Large) :
    0 < Real.log (3 * P.h) ∧ Real.log (3 * P.h) ≤ 2 * P.L := by
  obtain ⟨h1, h2⟩ := log_three_mul_h_bounds H G
  have h6 := log_six_le'
  have := G.L_ge
  constructor <;> linarith

def indexDenominator (P : Par) : ℝ := (P.k : ℝ) * ((P.m : ℝ) + (P.t : ℝ)) * Real.log (3 * P.h)

theorem lJ_eq_div (P : Par) : P.lJ = (P.m : ℝ) * P.b * P.L / indexDenominator P := rfl

theorem lJDenom_pos {P : Par} (H : P.Hyp) (G : P.Large) : 0 < indexDenominator P := by
  have nb := natBounds H
  obtain ⟨c1, _⟩ := log_three_mul_h_pos_le H G
  unfold indexDenominator
  exact mul_pos (mul_pos (by linarith [nb.k1]) (by linarith [nb.m1, nb.t6])) c1

theorem lJDenom_le {P : Par} (H : P.Hyp) (G : P.Large) :
    indexDenominator P ≤ 4 * (P.k : ℝ) * (P.t : ℝ) * P.L := by
  have nb := natBounds H
  have hk : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  have a : (P.m : ℝ) + P.t ≤ 2 * P.t := by linarith [nb.mt, nb.m1]
  obtain ⟨c1, c2⟩ := log_three_mul_h_pos_le H G
  have e : ((P.m : ℝ) + P.t) * Real.log (3 * P.h) ≤ (2 * P.t) * (2 * P.L) :=
    mul_le_mul a c2 c1.le (by linarith [nb.t6])
  have := mul_le_mul_of_nonneg_left e hk
  unfold indexDenominator
  nlinarith

theorem paramsLog_holds : Elem_a := by
  intro P H G
  have nb := natBounds H
  have hb := b_pos' P
  obtain ⟨h1, h2⟩ := log_three_mul_h_bounds H G
  obtain ⟨c1, c2⟩ := log_three_mul_h_pos_le H G
  have h6 := log_six_le'
  have hL := G.L_ge
  refine ⟨h2, by linarith, ?_⟩
  rw [lJ_eq_div, div_le_iff₀ (lJDenom_pos H G)]
  unfold indexDenominator
  have e1 : (P.m : ℝ) ≤ P.k * (P.m + P.t) := by
    nlinarith [nb.mlek, nb.k1, nb.t6, nb.m1]
  have e2 : (P.m : ℝ) * P.L ≤ P.k * (P.m + P.t) * Real.log (3 * P.h) :=
    mul_le_mul e1 h1 (by linarith) (by nlinarith [nb.k1, nb.t6, nb.m1])
  nlinarith [mul_le_mul_of_nonneg_left e2 hb.le]

theorem seven_lt_lstar {P : Par} (H : P.Hyp) (G : P.Large) : 7 < P.lstar := by
  have h2 := H.win_lt
  have hη := eta_nonneg' H
  have hbl := b_div_lstar_pos H G
  have ht : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  have e : 8 * P.b / P.lstar = 8 * (P.b / P.lstar) := by ring
  linarith

private theorem div_le_div_of_le_of_pos {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (hcb : c ≤ b) :
    a / b ≤ a / c := by
  calc a / b = a * (1 / b) := by ring
    _ ≤ a * (1 / c) := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hc hcb) ha
    _ = a / c := by ring

private theorem lJDenom_le_lstarDenom {P : Par} (H : P.Hyp) (G : P.Large) :
    indexDenominator P ≤ lstarDenom P := by
  have nb := natBounds H
  have hL := G.L_ge
  have hS := H.S_nonneg
  have hk0 : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  have hN : (P.k : ℝ) ≤ P.N + P.t := by
    unfold Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.N
    have : 0 ≤ (P.m : ℝ) * (P.t + 1) := by positivity
    linarith
  have h4 : (4 : ℝ) ≤ P.t * P.L := by nlinarith [nb.t6]
  have h0 : 0 ≤ (P.k : ℝ) * P.t * P.L := mul_nonneg (mul_nonneg hk0 ht0) (by linarith)
  have e1 := mul_le_mul_of_nonneg_left h4 h0
  have hkn : (P.k : ℝ) ≤ P.n * (P.N + P.t) := by
    nlinarith [mul_nonneg (sub_nonneg.2 nb.n1) (le_trans hk0 hN)]
  have e2 := mul_le_mul_of_nonneg_left hkn (by positivity : (0 : ℝ) ≤ (P.t : ℝ) ^ 2 * P.L ^ 2)
  have e3 : 0 ≤ (P.k : ℝ) * (P.n : ℝ) ^ 2 * (P.S + P.t + P.L) :=
    mul_nonneg (by positivity) (by linarith)
  have e4 := lJDenom_le H G
  unfold lstarDenom
  nlinarith

theorem paramsLStar_holds : Elem_b := by
  intro P H G
  have hJ := lJDenom_pos H G
  have hb := b_pos' P
  have nb := natBounds H
  have hL := G.L_ge
  have h7 := seven_lt_lstar H G
  refine ⟨?_, by nlinarith⟩
  have key := lJDenom_le_lstarDenom H G
  rw [lstar_eq_div, lJ_eq_div]
  calc P.L * ((P.m : ℝ) * P.b / lstarDenom P) = (P.m : ℝ) * P.b * P.L / lstarDenom P := by ring
    _ ≤ (P.m : ℝ) * P.b * P.L / indexDenominator P :=
        div_le_div_of_le_of_pos
          (mul_nonneg (mul_nonneg (by linarith [nb.m1]) hb.le) (by linarith)) hJ key

private theorem div_le_div_of_le_of_nonneg_right {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hab (inv_nonneg.2 hc)

theorem b_div_le_lJ {P : Par} (H : P.Hyp) (G : P.Large) :
    P.b / (4 * (P.k : ℝ) * (P.t : ℝ)) ≤ P.lJ := by
  have nb := natBounds H
  have hb := b_pos' P
  have hL := G.L_ge
  have hJ := lJDenom_pos H G
  have hkt : 0 < 4 * (P.k : ℝ) * (P.t : ℝ) :=
    mul_pos (mul_pos (by norm_num) (by linarith [nb.k1])) (by linarith [nb.t6])
  calc P.b / (4 * (P.k : ℝ) * (P.t : ℝ)) ≤ (P.m : ℝ) * P.b / (4 * (P.k : ℝ) * (P.t : ℝ)) :=
        div_le_div_of_le_of_nonneg_right (by nlinarith [nb.m1]) hkt.le
    _ = (P.m : ℝ) * P.b * P.L / (4 * (P.k : ℝ) * (P.t : ℝ) * P.L) :=
        (mul_div_mul_right _ _ (by linarith : P.L ≠ 0)).symm
    _ ≤ (P.m : ℝ) * P.b * P.L / indexDenominator P :=
        div_le_div_of_le_of_pos
          (mul_nonneg (mul_nonneg (by linarith [nb.m1]) hb.le) (by linarith)) hJ
          (lJDenom_le H G)
    _ = P.lJ := (lJ_eq_div P).symm

theorem kmax_le {P : Par} (H : P.Hyp) (G : P.Large) :
    (P.kmax : ℝ) ≤ 2 * (P.b / P.lstar) := by
  have hbl := b_div_lstar_pos H G
  have h0 : (0 : ℝ) ≤ 2 * P.b / P.lstar := by rw [mul_div_assoc]; linarith
  calc (P.kmax : ℝ) = ((⌊2 * P.b / P.lstar⌋₊ : ℕ) : ℝ) := rfl
    _ ≤ 2 * P.b / P.lstar := Nat.floor_le h0
    _ = 2 * (P.b / P.lstar) := by ring

private theorem size_bounds_of_large {P : Par} (H : P.Hyp) (G : P.Large) :
    P.S + P.η < P.lstar ∧ 2 * P.η + P.t + 8 * (P.b / P.lstar) + 7 < P.lstar ∧
      2 * P.lstar ≤ P.b ∧ 0 < P.b / P.lstar ∧ (P.kmax : ℝ) ≤ 2 * (P.b / P.lstar) ∧
      P.h = P.b + P.S + P.η + P.t + 1 ∧ 0 ≤ P.η ∧ (P.t : ℝ) ≤ P.η ∧ 0 ≤ P.S ∧ 0 < P.lstar := by
  have h1 := H.sum_lt
  have h2 := H.win_lt
  have hb' := H.b'_pos
  have hbl := b_div_lstar_pos H G
  have e : 8 * P.b / P.lstar = 8 * (P.b / P.lstar) := by ring
  exact ⟨by linarith, by linarith, two_mul_lstar_le_b H G, hbl, kmax_le H G, rfl, eta_nonneg' H,
    H.t_le, H.S_nonneg, lstar_pos H G⟩

theorem paramsLJ_holds : Elem_c := by
  intro P H G
  have nb := natBounds H
  have hb := b_pos' P
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := size_bounds_of_large H G
  have hc := b_div_le_lJ H G
  have hkt : 0 < 4 * (P.k : ℝ) * (P.t : ℝ) :=
    mul_pos (mul_pos (by norm_num) (by linarith [nb.k1])) (by linarith [nb.t6])
  have hc0 : 0 ≤ P.b / (4 * (P.k : ℝ) * (P.t : ℝ)) := div_nonneg hb.le hkt.le
  have hsq : 3 * P.b < (P.b / (4 * (P.k : ℝ) * (P.t : ℝ))) ^ 2 := by
    rw [div_pow, lt_div_iff₀ (pow_pos hkt 2)]
    have := mul_lt_mul_of_pos_left G.b_gt hb
    linarith
  have hsq2 := mul_self_le_mul_self hc0 hc
  have hNr := nb.nr2
  have hbl8 : 8 * (P.b / P.lstar) < P.lstar := by linarith
  have hbl2 : P.b / P.lstar * 8 ≤ P.b / 2 := by nlinarith
  refine ⟨hc, by linarith, ?_, ?_⟩
  · rw [a6]; linarith
  · linarith

theorem lstar_add_one_lt_lJ {P : Par} (H : P.Hyp) (G : P.Large) : P.lstar + 1 < P.lJ := by
  obtain ⟨h1, h2⟩ := paramsLStar_holds P H G
  linarith

theorem paramsLargePrime_holds : Elem_d := by
  intro P H G l hl
  have nb := natBounds H
  have hb := b_pos' P
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := size_bounds_of_large H G
  have hJ := lstar_add_one_lt_lJ H G
  have hLJ := paramsLJ_holds P H G
  have hbasic := paramsBasic_holds P H G
  have hl1 : P.lstar ≤ (l : ℝ) - 1 := by linarith
  have hl1p : 0 < (l : ℝ) - 1 := by linarith
  have hq : P.h / ((l : ℝ) - 1) ≤ 2 * P.b / P.lstar := by
    rw [div_le_div_iff₀ hl1p a10]
    nlinarith [mul_le_mul_of_nonneg_right hbasic.2.2 a10.le,
      mul_le_mul_of_nonneg_left hl1 (by linarith : (0 : ℝ) ≤ 2 * P.b)]
  have hkap : (P.kap l : ℝ) ≤ 2 * P.b / P.lstar := by
    have h0 : 0 ≤ P.h / ((l : ℝ) - 1) := div_nonneg (by linarith) hl1p.le
    exact le_trans (Nat.floor_le h0) hq
  have e2 : 2 * P.b / P.lstar = 2 * (P.b / P.lstar) := by ring
  have hkapmax : P.kap l ≤ P.kmax := Nat.floor_mono hq
  have hNr := nb.nr
  refine ⟨hl1, hkap, hkapmax, ?_, by linarith, ?_, by linarith [nb.kt, nb.m1], ?_⟩
  · have : (P.t : ℝ) + 2 * (P.kap l : ℝ) < l := by linarith
    exact_mod_cast this
  · have : (P.Nr : ℝ) + 1 < l := by linarith [nb.mlek, nb.kt]
    exact_mod_cast this
  · have hl0 : 0 < P.lJ := by linarith
    have := mul_self_lt_mul_self hl0.le hl
    linarith [hLJ.2.1, hLJ.2.2.1]

theorem paramsTop_holds : Elem_e := by
  intro P H G
  have nb := natBounds H
  have hc := b_div_le_lJ H G
  have hkt : 0 < 4 * (P.k : ℝ) * (P.t : ℝ) :=
    mul_pos (mul_pos (by norm_num) (by linarith [nb.k1])) (by linarith [nb.t6])
  have : 3 * P.b' < P.b / (4 * (P.k : ℝ) * (P.t : ℝ)) := by
    rw [lt_div_iff₀ hkt]
    nlinarith [G.bb']
  linarith

theorem paramsThin_holds : Elem_f := by
  intro P H G
  have nb := natBounds H
  have hw := G.w_gt
  have hk := kmax_le H G
  have e2 : 2 * P.b / P.lstar = 2 * (P.b / P.lstar) := by ring
  refine ⟨by linarith, ?_⟩
  unfold Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.w''
  exact div_le_self H.b'_pos.le (by nlinarith [H.x_ge, nb.n1])

theorem noWindowResidue_holds : NoResidueInWindow := by
  intro P H G l hl hlJ U bot c e σ hS hK
  have nb := natBounds H
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := size_bounds_of_large H G
  obtain ⟨hlst, hkap2, hkapmax, htk, hetk, hNr, hSk, hhN⟩ := paramsLargePrime_holds P H G l hlJ
  have hT := paramsTop_holds P H G
  obtain ⟨hth1, hth2⟩ := paramsThin_holds P H G
  have hw := G.w_gt
  have htop := G.top_le
  have hx := H.x_ge
  have hb' := H.b'_pos
  have e2 : 2 * P.b / P.lstar = 2 * (P.b / P.lstar) := by ring
  have hkapR : (P.kap l : ℝ) ≤ P.kmax := by exact_mod_cast hkapmax
  have hxinv : 0 ≤ P.b' / P.x := div_nonneg hb'.le (by linarith)
  have hxinv2 : 0 ≤ P.b' / P.x ^ 2 := div_nonneg hb'.le (by positivity)
  have htopE : P.b' * (1 + 1 / P.x + 1 / P.x ^ 2) = P.b' + P.b' / P.x + P.b' / P.x ^ 2 := by ring
  have htopE2 : P.b' * (1 + 1 / P.x ^ 2) = P.b' + P.b' / P.x ^ 2 := by ring
  have ht0 : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  obtain ⟨hσ, hc, hU⟩ := hS
  have hσabs : |(σ : ℝ)| = 1 := by rcases hσ with h | h <;> simp [h]
  refine Formalism.CohomologicalDescent.windowResidueCountEqZero_holds l bot P.t (P.kap l) U ?_
  intro u hu hun x hx'
  rw [Finset.mem_Icc] at hx'
  have hx1 : (bot : ℝ) - P.kap l ≤ x := by exact_mod_cast hx'.1
  have hx2 : (x : ℝ) ≤ bot + P.t - 1 + P.kap l := by exact_mod_cast hx'.2
  have hdabs : |(σ : ℝ) * ((x : ℝ) - (bot + ((P.t : ℝ) - 1) / 2))| ≤ ((P.t : ℝ) - 1) / 2 + P.kap l := by
    rw [abs_mul, hσabs, one_mul, abs_le]
    constructor <;> linarith
  have hd := abs_le.1 hdabs
  have hyx : (σ : ℝ) * ((u : ℝ) - x) = (σ : ℝ) * ((u : ℝ) - c) + e
      - (σ : ℝ) * ((x : ℝ) - (bot + ((P.t : ℝ) - 1) / 2)) := by
    linear_combination (-1 : ℝ) * hc
  have habs : |((u - x : ℤ) : ℝ)| = |(σ : ℝ) * ((u : ℝ) - x)| := by
    rw [abs_mul, hσabs, one_mul, Int.cast_sub]
  have fin : 0 < |(σ : ℝ) * ((u : ℝ) - x)| → |(σ : ℝ) * ((u : ℝ) - x)| < l →
      (0 < |u - x| ∧ |u - x| < (l : ℤ)) := by
    intro h1 h2
    rw [← habs] at h1 h2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  rcases hU u hu hun with ⟨hv0, hvS⟩ | ⟨hA1, hA2⟩
  · rcases hK with ⟨⟨hTh1, hTh2⟩, hEx⟩ | ⟨bt, hbt1, hbt2, hbt3, hbt4⟩ | ⟨hTn1, hTn2⟩
    · right
      intro hdvd
      apply hEx
      refine ⟨σ * (u - x), ?_, ?_, Dvd.dvd.mul_left hdvd σ⟩
      · push_cast
        linarith
      · push_cast
        linarith
    · left
      have ylo : 0 < (σ : ℝ) * ((u : ℝ) - x) := by rw [hyx]; linarith
      have yhi : (σ : ℝ) * ((u : ℝ) - x) < l := by rw [hyx]; linarith
      exact fin (by rw [abs_of_pos ylo]; exact ylo) (by rw [abs_of_pos ylo]; exact yhi)
    · left
      have ylo : 0 < (σ : ℝ) * ((u : ℝ) - x) := by rw [hyx]; linarith
      have yhi : (σ : ℝ) * ((u : ℝ) - x) < l := by rw [hyx]; linarith
      exact fin (by rw [abs_of_pos ylo]; exact ylo) (by rw [abs_of_pos ylo]; exact yhi)
  · left
    have hy : (σ : ℝ) * ((u : ℝ) - x) = ((σ : ℝ) * ((u : ℝ) - c) + e)
        - (σ : ℝ) * ((x : ℝ) - (bot + ((P.t : ℝ) - 1) / 2)) := by rw [hyx]
    have h1 := abs_sub_abs_le_abs_sub ((σ : ℝ) * ((u : ℝ) - c) + e)
      ((σ : ℝ) * ((x : ℝ) - (bot + ((P.t : ℝ) - 1) / 2)))
    rw [← hy] at h1
    have hA2' := abs_le.1 hA2
    exact fin (by linarith) (abs_lt.2 ⟨by linarith, by linarith⟩)

theorem exceptionalRange_holds : ExceptionalRange := by
  intro P H G z hz1 hz2
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := size_bounds_of_large H G
  have hLJ := paramsLJ_holds P H G
  have ht0 : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  constructor
  · have : (0 : ℝ) < z := by linarith
    exact_mod_cast this
  · linarith [hLJ.2.2.2, hLJ.2.1]

private theorem toNat_cast_le_of_le {a : ℤ} {r : ℝ} (h : (a : ℝ) ≤ r) (hr : 0 ≤ r) : ((a.toNat : ℕ) : ℝ) ≤ r := by
  rcases le_or_gt 0 a with h0 | h0
  · have e : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h0
    have e' : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by exact_mod_cast e
    rw [e']
    exact h
  · have : a.toNat = 0 := by omega
    rw [this, Nat.cast_zero]
    exact hr

theorem exceptionalCount_holds : ExceptionalCount := by
  intro P H G Q hQ
  have hJ0 : 0 ≤ P.lJ := by linarith [lstar_add_one_lt_lJ H G, lstar_pos H G]
  have hP : ∀ l ∈ Q, l.Prime ∧ P.lJ < (l : ℝ) ∧ ∃ n ∈ Finset.Icc
      ⌈P.b - ((P.t : ℝ) - 1) / 2 - (P.kmax : ℝ)⌉
      ⌊P.b + P.S + P.η + 1 + ((P.t : ℝ) - 1) / 2 + (P.kmax : ℝ)⌋, (l : ℤ) ∣ n := by
    intro l hl
    obtain ⟨hp, hlt, z, hz1, hz2, hz3⟩ := hQ l hl
    exact ⟨hp, hlt, z, Finset.mem_Icc.2 ⟨Int.ceil_le.2 hz1, Int.le_floor.2 hz2⟩, hz3⟩
  have hTT : ∀ n ∈ Finset.Icc
      ⌈P.b - ((P.t : ℝ) - 1) / 2 - (P.kmax : ℝ)⌉
      ⌊P.b + P.S + P.η + 1 + ((P.t : ℝ) - 1) / 2 + (P.kmax : ℝ)⌋,
      n ≠ 0 ∧ ((|n| : ℤ) : ℝ) < P.lJ ^ 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨h1, h2⟩ := exceptionalRange_holds P H G n (Int.ceil_le.1 hn.1) (Int.le_floor.1 hn.2)
    refine ⟨h1.ne', ?_⟩
    rw [abs_of_pos h1]
    exact h2
  have hc := Formalism.CohomologicalDescent.largePrimeDivisorCount_holds P.lJ _ Q hJ0 hTT hP
  rw [Int.card_Icc] at hc
  have hcR : (Q.card : ℝ) ≤ ((⌊P.b + P.S + P.η + 1 + ((P.t : ℝ) - 1) / 2 + (P.kmax : ℝ)⌋ + 1
      - ⌈P.b - ((P.t : ℝ) - 1) / 2 - (P.kmax : ℝ)⌉).toNat : ℝ) := by exact_mod_cast hc
  have hfl := Int.floor_le (P.b + P.S + P.η + 1 + ((P.t : ℝ) - 1) / 2 + (P.kmax : ℝ))
  have hce := Int.le_ceil (P.b - ((P.t : ℝ) - 1) / 2 - (P.kmax : ℝ))
  have hS := H.S_nonneg
  have hη := eta_nonneg' H
  have ht0 : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ P.kmax := Nat.cast_nonneg _
  have hfin := toNat_cast_le_of_le (a := ⌊P.b + P.S + P.η + 1 + ((P.t : ℝ) - 1) / 2 + (P.kmax : ℝ)⌋ + 1
      - ⌈P.b - ((P.t : ℝ) - 1) / 2 - (P.kmax : ℝ)⌉)
      (r := P.S + P.η + (P.t : ℝ) + 2 * (P.kmax : ℝ) + 1) (by push_cast; linarith) (by linarith)
  linarith

theorem noWindowOf_holds : NoWindowOf := by
  intro P H G ι D pl l hl hlJ hEx τ
  have kind : ∀ e : ℝ, (P.Thick e ∨ P.Top e ∨ P.Thin e) →
      ((P.Thick e ∧ ¬ P.Excl l) ∨ P.Top e ∨ P.Thin e) := by
    intro e h
    rcases h with h | h | h
    · exact Or.inl ⟨h, hEx⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  constructor
  · rw [pl.mw_eq τ l]
    exact noWindowResidue_holds P H G l hl hlJ _ _ _ _ _ (pl.shape τ) (kind _ (pl.kind τ))
  · rw [pl.mwF_eq τ l]
    exact noWindowResidue_holds P H G l hl hlJ _ _ _ _ _ (pl.shapeF τ l) (kind _ (pl.kindF τ l))

theorem mem_primesLe {y : ℝ} (hy : 0 ≤ y) {p : ℕ} : p ∈ pr y ↔ p.Prime ∧ (p : ℝ) ≤ y := by
  unfold pr
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff, Nat.le_floor_iff hy]
  exact and_comm

theorem subset_primesLe {y : ℝ} (hy : 0 ≤ y) {Q : Finset ℕ} (hQ : ∀ l ∈ Q, l.Prime ∧ (l : ℝ) ≤ y) :
    Q ⊆ pr y := fun l hl => (mem_primesLe hy).2 (hQ l hl)

theorem prime_of_mem_primesLe {y : ℝ} {p : ℕ} (hp : p ∈ pr y) : p.Prime :=
  (Finset.mem_filter.1 hp).2

theorem two_le_prime_cast {p : ℕ} (hp : p.Prime) : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le

theorem log_prime_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) :=
  Real.log_nonneg (by have := two_le_prime_cast hp; linarith)

theorem choose_two_le_sq_div_two (n : ℕ) : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
  have h1 : 2 * n.choose 2 ≤ n ^ 2 := by
    rw [Nat.choose_two_right]
    calc 2 * (n * (n - 1) / 2) = (n * (n - 1) / 2) * 2 := by ring
      _ ≤ n * (n - 1) := Nat.div_mul_le_self _ _
      _ ≤ n * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = n ^ 2 := by ring
  have h2 : (2 : ℝ) * (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast h1
  linarith

theorem hw_le_two_mul_b' {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι} (hW : D.Widths P)
    {τ : ι} (hτ : τ ∉ D.T2) : D.hw τ ≤ 2 * P.b' := by
  have htop := G.top_le
  have hth := (paramsThin_holds P H G).2
  have hb' := H.b'_pos
  have hx := H.x_ge
  have hxinv : 0 ≤ P.b' / P.x := div_nonneg hb'.le (by linarith)
  have hxinv2 : 0 ≤ P.b' / P.x ^ 2 := div_nonneg hb'.le (by positivity)
  have htopE : P.b' * (1 + 1 / P.x + 1 / P.x ^ 2) = P.b' + P.b' / P.x + P.b' / P.x ^ 2 := by ring
  rcases hW τ hτ with h | h <;> linarith

theorem thinSum_holds : SumA := by
  intro hpc P H G ι D hA hW τ hτ Q hQ
  have hb' := H.b'_pos
  have hRHS : 0 ≤ 1.3 * (P.Nr : ℝ) ^ 2 * P.b' := mul_nonneg (by positivity) hb'.le
  have hhw := hw_le_two_mul_b' H G hW hτ
  by_cases hw1 : D.hw τ ≤ 1
  · have : ∑ l ∈ Q, (D.ex τ l : ℝ) * Real.log (l : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      have h2 := two_le_prime_cast (hQ l hl)
      rw [(hA τ hτ l (hQ l hl)).1 (by linarith), Nat.cast_zero, zero_mul]
    rw [this]
    exact hRHS
  · push_neg at hw1
    have hlogpos : 0 < Real.log (D.hw τ) := Real.log_pos hw1
    have hC := choose_two_le_sq_div_two P.Nr
    have hC0 : (0 : ℝ) ≤ (P.Nr.choose 2 : ℝ) := Nat.cast_nonneg _
    have hsub : Q.filter (fun l : ℕ => (l : ℝ) ≤ D.hw τ) ⊆ pr (D.hw τ) :=
      subset_primesLe (by linarith) (fun l hl => by
        rw [Finset.mem_filter] at hl
        exact ⟨hQ l hl.1, hl.2⟩)
    have hcard : ((Q.filter (fun l : ℕ => (l : ℝ) ≤ D.hw τ)).card : ℝ) ≤ ((pr (D.hw τ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hpcb := hpc (D.hw τ) hw1
    have hne := hlogpos.ne'
    have hM : 0 ≤ (P.Nr.choose 2 : ℝ) * Real.log (D.hw τ) := mul_nonneg hC0 hlogpos.le
    calc ∑ l ∈ Q, (D.ex τ l : ℝ) * Real.log (l : ℝ)
        = ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ D.hw τ), (D.ex τ l : ℝ) * Real.log (l : ℝ) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro l hl
          split_ifs with h
          · rfl
          · rw [(hA τ hτ l (hQ l hl)).1 (not_le.1 h), Nat.cast_zero, zero_mul]
      _ ≤ ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ D.hw τ), (P.Nr.choose 2 : ℝ) * Real.log (D.hw τ) := by
          apply Finset.sum_le_sum
          intro l hl
          rw [Finset.mem_filter] at hl
          exact (hA τ hτ l (hQ l hl.1)).2 hl.2
      _ = ((Q.filter (fun l : ℕ => (l : ℝ) ≤ D.hw τ)).card : ℝ) * ((P.Nr.choose 2 : ℝ) * Real.log (D.hw τ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((pr (D.hw τ)).card : ℝ) * ((P.Nr.choose 2 : ℝ) * Real.log (D.hw τ)) :=
          mul_le_mul_of_nonneg_right hcard hM
      _ ≤ (1.26 * D.hw τ / Real.log (D.hw τ)) * ((P.Nr.choose 2 : ℝ) * Real.log (D.hw τ)) :=
          mul_le_mul_of_nonneg_right hpcb.le hM
      _ = 1.26 * D.hw τ * (P.Nr.choose 2 : ℝ) := by
          field_simp
          try ring
      _ ≤ 1.3 * (P.Nr : ℝ) ^ 2 * P.b' := by
          have k1 := mul_le_mul hhw hC hC0 (by linarith : (0 : ℝ) ≤ 2 * P.b')
          have k2 : 0 ≤ D.hw τ * (P.Nr.choose 2 : ℝ) := mul_nonneg (by linarith) hC0
          have k3 : 0 ≤ P.b' * (P.Nr : ℝ) ^ 2 := mul_nonneg hb'.le (sq_nonneg _)
          have d1 : (1.26 : ℝ) = 63 / 50 := by norm_num
          have d2 : (1.3 : ℝ) = 13 / 10 := by norm_num
          rw [d1, d2]
          nlinarith

theorem log_h_bounds {P : Par} (H : P.Hyp) (G : P.Large) :
    0 < Real.log P.h ∧ Real.log P.h ≤ P.L + 0.7 := by
  have hb := b_pos' P
  have hh := (paramsBasic_holds P H G).2.2
  have h7 := b_add_seven_le_h H
  have h2 := log_two_le_seven_tenths
  constructor
  · exact Real.log_pos (by linarith)
  · have : Real.log P.h ≤ P.L + 7 / 10 := by
      calc Real.log P.h ≤ Real.log (2 * P.b) := Real.log_le_log (by linarith) hh
        _ = Real.log 2 + P.L := by rw [Real.log_mul (by norm_num) hb.ne', log_b']
        _ ≤ P.L + 7 / 10 := by linarith
    have d : (0.7 : ℝ) = 7 / 10 := by norm_num
    rw [d]
    exact this

private theorem log_h_pos_and_le {P : Par} (H : P.Hyp) (G : P.Large) :
    0 < Real.log P.h ∧ Real.log P.h ≤ P.L + 7 / 10 := by
  obtain ⟨h1, h2⟩ := log_h_bounds H G
  have d : (0.7 : ℝ) = 7 / 10 := by norm_num
  rw [d] at h2
  exact ⟨h1, h2⟩

theorem ex_mul_log_le_of_thickA {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι}
    (hA : D.ThickA P) {τ : ι} (hτ : τ ∈ D.T2) {l : ℕ} (hl : l.Prime) :
    (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ (P.Nr : ℝ) ^ 2 * P.L := by
  obtain ⟨_, h2, _⟩ := hA τ hτ l hl
  obtain ⟨c1, c2⟩ := log_h_pos_and_le H G
  have hC := choose_two_le_sq_div_two P.Nr
  have hL := G.L_ge
  calc (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ (P.Nr.choose 2 : ℝ) * Real.log P.h := h2
    _ ≤ ((P.Nr : ℝ) ^ 2 / 2) * (P.L + 7 / 10) := mul_le_mul hC c2 c1.le (by positivity)
    _ ≤ (P.Nr : ℝ) ^ 2 * P.L := by
        nlinarith [mul_nonneg (sq_nonneg (P.Nr : ℝ)) (by linarith : (0 : ℝ) ≤ P.L / 2 - 7 / 20)]

theorem smaller_exponent_lt {P : Par} (H : P.Hyp) (G : P.Large) : P.b' < P.b := by
  have nb := natBounds H
  have hb' := H.b'_pos
  have h1 : (1 : ℝ) ≤ 12 * P.k * P.t := by nlinarith [nb.k1, nb.t6]
  have := mul_le_mul_of_nonneg_right h1 hb'.le
  linarith [G.bb']

theorem ex_mul_log_le_of_thinA {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι}
    (hA : D.ThinA P) (hW : D.Widths P) {τ : ι} (hτ : τ ∉ D.T2) {l : ℕ} (hl : l.Prime) :
    (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ (P.Nr : ℝ) ^ 2 * P.L := by
  obtain ⟨h1, h2⟩ := hA τ hτ l hl
  have hl2 := two_le_prime_cast hl
  have hL := G.L_ge
  by_cases hlw : D.hw τ < l
  · rw [h1 hlw, Nat.cast_zero, zero_mul]
    exact mul_nonneg (sq_nonneg _) (by linarith)
  · push_neg at hlw
    have hhw := hw_le_two_mul_b' H G hW hτ
    have hbb := smaller_exponent_lt H G
    have hb := b_pos' P
    have h2' := log_two_le_seven_tenths
    have hlog : Real.log (D.hw τ) ≤ 2 * P.L := by
      calc Real.log (D.hw τ) ≤ Real.log (2 * P.b) := Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 2 + P.L := by rw [Real.log_mul (by norm_num) hb.ne', log_b']
        _ ≤ 2 * P.L := by linarith
    have hlog0 : 0 ≤ Real.log (D.hw τ) := Real.log_nonneg (by linarith)
    have hC := choose_two_le_sq_div_two P.Nr
    calc (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ (P.Nr.choose 2 : ℝ) * Real.log (D.hw τ) := h2 hlw
      _ ≤ ((P.Nr : ℝ) ^ 2 / 2) * (2 * P.L) := mul_le_mul hC hlog hlog0 (by positivity)
      _ = (P.Nr : ℝ) ^ 2 * P.L := by ring

theorem costBound_holds : CostB := by
  intro P H G ι _ D hcard hA hK hW l hl
  rw [Finset.sum_mul]
  calc ∑ τ, (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ ∑ _τ : ι, (P.Nr : ℝ) ^ 2 * P.L := by
        apply Finset.sum_le_sum
        intro τ _
        by_cases hτ : τ ∈ D.T2
        · exact ex_mul_log_le_of_thickA H G hK hτ hl
        · exact ex_mul_log_le_of_thinA H G hA hW hτ hl
    _ = (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L := by
        rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
        ring

theorem thickTerm_holds : TermC := by
  intro P H G ι D hA τ hτ l hl hlJ
  have nb := natBounds H
  have hb := b_pos' P
  have hL := G.L_ge
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := size_bounds_of_large H G
  obtain ⟨h1, h2, h3⟩ := hA τ hτ l hl
  have hl2 := two_le_prime_cast hl
  have hl0 : (0 : ℝ) < l := by linarith
  have hJpos := lJDenom_pos H G
  have hJeq : P.lJ * indexDenominator P = P.m * P.b * P.L := by
    rw [lJ_eq_div]
    field_simp
  have hlog0 := log_prime_nonneg hl
  have hex0 : (0 : ℝ) ≤ D.ex τ l := Nat.cast_nonneg _
  rw [le_div_iff₀ hl0]
  by_cases hbig : 2 * P.η + P.t ≤ l
  · have h3' := h3 hbig
    have hk1 := nb.k1
    have hSk : 1 ≤ P.S + P.k := by linarith
    have hSk3 : P.S + P.k ≤ 3 * P.h := by rw [a6]; linarith [nb.kt, nb.m1, hb]
    have hlg : Real.log (P.S + P.k) ≤ Real.log (3 * P.h) := Real.log_le_log (by linarith) hSk3
    have hlg0 : 0 ≤ Real.log (P.S + P.k) := Real.log_nonneg hSk
    have hkk : (P.k : ℝ) ^ 2 ≤ P.k * (P.m + P.t) := by
      nlinarith [nb.kt, nb.m1]
    have e1 : (P.k : ℝ) ^ 2 * Real.log (P.S + P.k) ≤ P.k * (P.m + P.t) * Real.log (3 * P.h) :=
      mul_le_mul hkk hlg hlg0 (by positivity)
    have e2 : (D.ex τ l : ℝ) * Real.log l ≤ 2 * indexDenominator P := by
      unfold indexDenominator
      linarith
    have e3 : indexDenominator P * l ≤ indexDenominator P * P.lJ := mul_le_mul_of_nonneg_left hlJ hJpos.le
    have e4 := mul_le_mul_of_nonneg_right e2 hl0.le
    linarith
  · push_neg at hbig
    have hl3 : (l : ℝ) < 3 * P.η := by linarith
    obtain ⟨c1, c2⟩ := log_h_pos_and_le H G
    have hC := choose_two_le_sq_div_two P.Nr
    have hNr2 : (P.Nr : ℝ) ^ 2 ≤ 4 * (P.t : ℝ) ^ 2 := by
      have := nb.nr2
      have h0 : (0 : ℝ) ≤ P.Nr := Nat.cast_nonneg _
      nlinarith
    have e1 : (D.ex τ l : ℝ) * Real.log l ≤ ((P.Nr : ℝ) ^ 2 / 2) * (2 * P.L) :=
      h2.trans (mul_le_mul hC (by linarith) c1.le (by positivity))
    have e1' : (D.ex τ l : ℝ) * Real.log l ≤ 4 * (P.t : ℝ) ^ 2 * P.L := by
      have := mul_le_mul_of_nonneg_right hNr2 (by linarith : (0 : ℝ) ≤ P.L)
      linarith
    have hpos : 0 < (P.t : ℝ) ^ 3 * P.f * (P.k : ℝ) ^ 3 :=
      mul_pos (mul_pos (pow_pos (by linarith [nb.t6]) 3) (by linarith [nb.f1]))
        (pow_pos (by linarith [nb.k1]) 3)
    have hηb : P.η * ((P.t : ℝ) ^ 3 * P.f * (P.k : ℝ) ^ 3) ≤ P.b := (le_div_iff₀ hpos).1 H.η_le
    have hk2 := mul_le_mul nb.k1 nb.k1 zero_le_one (by linarith [nb.k1])
    have hk3' := mul_le_mul hk2 nb.k1 zero_le_one (by nlinarith [nb.k1])
    have hk3 : (1 : ℝ) ≤ (P.k : ℝ) ^ 3 := by
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ (P.k : ℝ) * P.k * P.k := hk3'
        _ = (P.k : ℝ) ^ 3 := by ring
    have hmf1 := mul_le_mul nb.m1 nb.f1 zero_le_one (by linarith [nb.m1])
    have hmf : (1 : ℝ) ≤ P.m * P.f := by linarith
    have hmft1 := mul_le_mul hmf nb.t6 (by norm_num) (by linarith)
    have hmft : (6 : ℝ) ≤ P.m * P.f * P.t := by linarith
    have q6 := mul_le_mul hmft hk3 (by norm_num) (by linarith)
    have t2L : 0 ≤ 4 * (P.t : ℝ) ^ 2 * P.L := mul_nonneg (by positivity) (by linarith)
    have sa := mul_le_mul_of_nonneg_right e1' hl0.le
    have sb := mul_le_mul_of_nonneg_left hl3.le t2L
    have sc := mul_le_mul_of_nonneg_left q6
      (mul_nonneg (mul_nonneg (by positivity) (by linarith)) a7 : (0 : ℝ) ≤ 2 * (P.t : ℝ) ^ 2 * P.L * P.η)
    have sd := mul_le_mul_of_nonneg_left hηb (mul_nonneg (by positivity) (by linarith) : (0 : ℝ) ≤ 2 * (P.m : ℝ) * P.L)
    linarith

theorem eight_lt_lJ {P : Par} (H : P.Hyp) (G : P.Large) : 8 < P.lJ := by
  linarith [lstar_add_one_lt_lJ H G, seven_lt_lstar H G]

theorem log_lJ_bounds {P : Par} (H : P.Hyp) (G : P.Large) :
    2 < Real.log P.lJ ∧ Real.log P.lJ ≤ P.L := by
  have h8 := eight_lt_lJ H G
  have hLJb := (paramsLog_holds P H G).2.2
  constructor
  · have he : Real.exp 2 < 8 := by
      have h := Real.exp_one_lt_d9
      have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [e]
      norm_num at h
      nlinarith [Real.exp_pos 1]
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ < Real.log P.lJ := Real.log_lt_log (Real.exp_pos 2) (by linarith)
  · calc Real.log P.lJ ≤ Real.log P.b := Real.log_le_log (by linarith) hLJb
      _ = P.L := log_b' P

def gatedCoefficientTerm {ι : Type} (D : SizeData₂ ι) (P : Par) (τ : ι) (l : ℕ) : ℝ :=
  if ((d0 l (D.xlo τ - D.maxB τ) : ℕ) : ℤ) < D.xlo τ - D.maxB τ then
    min (min (P.k : ℝ) (P.t : ℝ)) ((D.q τ : ℝ) * P.h / (d0 l (D.xlo τ - D.maxB τ) : ℝ)) else 0

theorem cW_eq_of_eq_zero {ι : Type} (D : SizeData₂ ι) (P : Par) (τ : ι) (l : ℕ) (h1 : D.mw τ l = 0)
    (h2 : D.mwF τ l = 0) (h3 : D.ecl τ l = 0) :
    D.cW P τ l = ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * ((P.h + (P.Nr : ℝ)) / ((l : ℝ) - 1) + 6)
      + (P.k : ℝ) * (P.S / (l : ℝ) + IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ))
      + gatedCoefficientTerm D P τ l
      + ((D.q τ : ℝ) * P.h / (l : ℝ)) * (1 + max 0 (Real.log (P.h / (l : ℝ)))) := by
  simp only [SizeData₂.cW, SizeData₂.depth, gatedCoefficientTerm, h1, h2, h3, Nat.cast_zero, mul_zero, add_zero,
    zero_mul, zero_add]

theorem sum_min_cW_le_split {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι}
    (hA : D.ThickA P) (hC : D.CloudA P) (hNW : D.NoWindow P) {τ : ι} (hτ : τ ∈ D.T2)
    {Q : Finset ℕ} (hQ : ∀ l ∈ Q, l.Prime ∧ P.lJ < (l : ℝ) ∧ ¬ P.Excl l) :
    ∑ l ∈ Q, min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ) ≤
      ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (P.h + (P.Nr : ℝ)) *
          ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h), Real.log (l : ℝ) / ((l : ℝ) - 1)
      + 6 * ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) *
          ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h), Real.log (l : ℝ)
      + (P.k : ℝ) * P.S * ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h), Real.log (l : ℝ) / (l : ℝ)
      + (P.k : ℝ) * ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h),
          IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ) * Real.log (l : ℝ)
      + ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h), gatedCoefficientTerm D P τ l * Real.log (l : ℝ)
      + (D.q τ : ℝ) * P.h * ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h),
          (1 + max 0 (Real.log (P.h / (l : ℝ)))) * (Real.log (l : ℝ) / (l : ℝ)) := by
  calc ∑ l ∈ Q, min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ)
      ≤ ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h),
            (((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (P.h + (P.Nr : ℝ)) * (Real.log (l : ℝ) / ((l : ℝ) - 1))
              + 6 * ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * Real.log (l : ℝ)
              + (P.k : ℝ) * P.S * (Real.log (l : ℝ) / (l : ℝ))
              + (P.k : ℝ) * (Formalism.CohomologicalDescent.IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ) * Real.log (l : ℝ))
              + gatedCoefficientTerm D P τ l * Real.log (l : ℝ)
              + (D.q τ : ℝ) * P.h * ((1 + max 0 (Real.log (P.h / (l : ℝ)))) * (Real.log (l : ℝ) / (l : ℝ)))) := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro l hl
        obtain ⟨hp, hlJ, hEx⟩ := hQ l hl
        have hlog0 := log_prime_nonneg hp
        split_ifs with hlh
        · obtain ⟨_, _, _, _, _, _, hSk, _⟩ := paramsLargePrime_holds P H G l hlJ
          have hecl := hC τ hτ l hp hSk
          obtain ⟨hmw, hmwF⟩ := hNW l hp hlJ hEx τ
          have e := cW_eq_of_eq_zero D P τ l hmw hmwF hecl
          calc min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ) ≤ D.cW P τ l * Real.log (l : ℝ) :=
                mul_le_mul_of_nonneg_right (min_le_right _ _) hlog0
            _ = ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (P.h + (P.Nr : ℝ)) * (Real.log (l : ℝ) / ((l : ℝ) - 1))
              + 6 * ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * Real.log (l : ℝ)
              + (P.k : ℝ) * P.S * (Real.log (l : ℝ) / (l : ℝ))
              + (P.k : ℝ) * (Formalism.CohomologicalDescent.IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ) * Real.log (l : ℝ))
              + gatedCoefficientTerm D P τ l * Real.log (l : ℝ)
              + (D.q τ : ℝ) * P.h * ((1 + max 0 (Real.log (P.h / (l : ℝ)))) * (Real.log (l : ℝ) / (l : ℝ))) := by
                rw [e]
                ring
        · have hex := (hA τ hτ l hp).1 (not_le.1 hlh)
          rw [hex, Nat.cast_zero]
          nlinarith [min_le_left (0 : ℝ) (D.cW P τ l)]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem h_add_Nr_bounds {P : Par} (H : P.Hyp) (G : P.Large) :
    P.h ≤ P.h + (P.Nr : ℝ) ∧ 1 < P.h + (P.Nr : ℝ) ∧ P.h + (P.Nr : ℝ) ≤ 3 * P.b ∧
      0 < Real.log (P.h + (P.Nr : ℝ)) ∧ Real.log (P.h + (P.Nr : ℝ)) ≤ P.L + 1.1 := by
  have hb := b_pos' P
  have hLJ := paramsLJ_holds P H G
  have h7 := b_add_seven_le_h H
  have hNr0 : (0 : ℝ) ≤ P.Nr := Nat.cast_nonneg _
  have h3 := log_three_le_eleven_tenths
  refine ⟨by linarith, by linarith, hLJ.2.2.1, Real.log_pos (by linarith), ?_⟩
  have : Real.log (P.h + (P.Nr : ℝ)) ≤ P.L + 11 / 10 := by
    calc Real.log (P.h + (P.Nr : ℝ)) ≤ Real.log (3 * P.b) := Real.log_le_log (by linarith) hLJ.2.2.1
      _ = Real.log 3 + P.L := by rw [Real.log_mul (by norm_num) hb.ne', log_b']
      _ ≤ P.L + 11 / 10 := by linarith
  have d : (1.1 : ℝ) = 11 / 10 := by norm_num
  rw [d]
  exact this

theorem subset_primesLe_h_add_Nr {P : Par} (H : P.Hyp) (G : P.Large) {R : Finset ℕ}
    (hR : ∀ l ∈ R, l.Prime ∧ P.lJ < (l : ℝ) ∧ (l : ℝ) ≤ P.h) : R ⊆ pr (P.h + (P.Nr : ℝ)) := by
  have hb := b_pos' P
  have h7 := b_add_seven_le_h H
  have hNr0 : (0 : ℝ) ≤ P.Nr := Nat.cast_nonneg _
  exact subset_primesLe (by linarith) (fun l hl => ⟨(hR l hl).1, by linarith [(hR l hl).2.2]⟩)

theorem log_div_prime_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) / (p : ℝ) :=
  div_nonneg (log_prime_nonneg hp) (Nat.cast_nonneg _)

theorem floor_h_bounds {P : Par} (H : P.Hyp) (G : P.Large) :
    (1 : ℝ) ≤ (⌊P.h⌋₊ : ℝ) ∧ (⌊P.h⌋₊ : ℝ) ≤ P.h ∧ (⌊P.h⌋₊ : ℝ) < P.lJ ^ 2 ∧
      0 ≤ Real.log (⌊P.h⌋₊ : ℝ) ∧ Real.log (⌊P.h⌋₊ : ℝ) ≤ Real.log P.h := by
  have hb := b_pos' P
  have h7 := b_add_seven_le_h H
  have hh := (paramsBasic_holds P H G).2.2
  have hLJ := paramsLJ_holds P H G
  have hh0 : 0 ≤ P.h := by linarith
  have f1 : (1 : ℝ) ≤ (⌊P.h⌋₊ : ℝ) := by
    have : 1 ≤ ⌊P.h⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; linarith)
    exact_mod_cast this
  have f2 : (⌊P.h⌋₊ : ℝ) ≤ P.h := Nat.floor_le hh0
  exact ⟨f1, f2, by linarith [hLJ.2.1], Real.log_nonneg f1, Real.log_le_log (by linarith) f2⟩

theorem le_floor_h {P : Par} (H : P.Hyp) {z : ℤ} (hz : (z : ℝ) ≤ P.h) :
    z ≤ ((⌊P.h⌋₊ : ℕ) : ℤ) := by
  rcases le_or_gt z 0 with hz0 | hz0
  · have : (0 : ℤ) ≤ ((⌊P.h⌋₊ : ℕ) : ℤ) := by positivity
    linarith
  · have e : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
      have : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0.le
      exact_mod_cast this
    have h1 : z.toNat ≤ ⌊P.h⌋₊ := Nat.le_floor (by rw [e]; exact hz)
    omega

theorem sum_residueIndicator_mul_log_le {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι}
    (hT : D.ShapeT P) {τ : ι} (hτ : τ ∈ D.T2) {R : Finset ℕ}
    (hR : ∀ l ∈ R, l.Prime ∧ P.lJ < (l : ℝ) ∧ (l : ℝ) ≤ P.h) :
    ∑ l ∈ R, IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ) * Real.log (l : ℝ) ≤
      (P.S + 1) * Real.log P.h := by
  obtain ⟨hmb0, hmbx, hxx, hxh, hS, _⟩ := hT τ hτ
  have hJ8 := eight_lt_lJ H G
  obtain ⟨f1, f2, f3, f4, f5⟩ := floor_h_bounds H G
  have hxhN := le_floor_h H hxh
  have key := Formalism.CohomologicalDescent.residueIndicatorPrimeSum_holds ⌊P.h⌋₊ P.lJ (D.xlo τ) (D.xhi τ) (D.maxB τ) R
    (by linarith) f3 hmb0 hmbx hxx hxhN (fun l hl => ⟨(hR l hl).1, (hR l hl).2.1⟩)
  have hS0 := H.S_nonneg
  exact key.trans (mul_le_mul (by linarith) f5 f4 (by linarith))

theorem toNat_xlo_sub_maxB_bounds {P : Par} (H : P.Hyp) {ι : Type} {D : SizeData₂ ι}
    (hT : D.ShapeT P) {τ : ι} (hτ : τ ∈ D.T2) :
    (((D.xlo τ - D.maxB τ).toNat : ℕ) : ℤ) = D.xlo τ - D.maxB τ ∧
      1 ≤ (D.xlo τ - D.maxB τ).toNat ∧ (D.xlo τ - D.maxB τ).toNat ≤ ⌊P.h⌋₊ := by
  obtain ⟨hmb0, hmbx, hxx, hxh, _, _⟩ := hT τ hτ
  have hxhN := le_floor_h H hxh
  refine ⟨by omega, by omega, by omega⟩

theorem sum_gateTerm_mul_log_le {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι}
    (hT : D.ShapeT P) {τ : ι} (hτ : τ ∈ D.T2) {R : Finset ℕ}
    (hR : ∀ l ∈ R, l.Prime ∧ P.lJ < (l : ℝ) ∧ (l : ℝ) ≤ P.h) :
    ∑ l ∈ R, gatedCoefficientTerm D P τ l * Real.log (l : ℝ) ≤
      (D.q τ : ℝ) * P.h * (1 + Real.log P.h) * Real.log P.h := by
  obtain ⟨e, h1, h2⟩ := toNat_xlo_sub_maxB_bounds H hT hτ
  obtain ⟨f1, f2, f3, f4, f5⟩ := floor_h_bounds H G
  obtain ⟨c1, _⟩ := log_h_bounds H G
  have hJ8 := eight_lt_lJ H G
  have hA0 : 0 ≤ (D.q τ : ℝ) * P.h := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hk0 : 0 ≤ min (P.k : ℝ) (P.t : ℝ) := le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have key := Formalism.CohomologicalDescent.gatedPrimeSum_holds (D.xlo τ - D.maxB τ).toNat ⌊P.h⌋₊ P.lJ ((D.q τ : ℝ) * P.h)
    (min (P.k : ℝ) (P.t : ℝ)) R h1 h2 hA0 hk0 f3 (by linarith)
    (fun l hl => ⟨(hR l hl).1, (hR l hl).2.1⟩)
  rw [e] at key
  have key2 : ∑ l ∈ R, gatedCoefficientTerm D P τ l * Real.log (l : ℝ) ≤
      (D.q τ : ℝ) * P.h * (1 + Real.log (⌊P.h⌋₊ : ℝ)) * Real.log (⌊P.h⌋₊ : ℝ) := key
  have hm : (1 + Real.log (⌊P.h⌋₊ : ℝ)) * Real.log (⌊P.h⌋₊ : ℝ) ≤ (1 + Real.log P.h) * Real.log P.h :=
    mul_le_mul (by linarith) f5 f4 (by linarith)
  calc ∑ l ∈ R, gatedCoefficientTerm D P τ l * Real.log (l : ℝ)
      ≤ (D.q τ : ℝ) * P.h * (1 + Real.log (⌊P.h⌋₊ : ℝ)) * Real.log (⌊P.h⌋₊ : ℝ) := key2
    _ = (D.q τ : ℝ) * P.h * ((1 + Real.log (⌊P.h⌋₊ : ℝ)) * Real.log (⌊P.h⌋₊ : ℝ)) := by ring
    _ ≤ (D.q τ : ℝ) * P.h * ((1 + Real.log P.h) * Real.log P.h) := mul_le_mul_of_nonneg_left hm hA0
    _ = (D.q τ : ℝ) * P.h * (1 + Real.log P.h) * Real.log P.h := by ring

theorem sum_one_add_log_div_le {P : Par} {R : Finset ℕ}
    (hR : ∀ l ∈ R, l.Prime ∧ P.lJ < (l : ℝ) ∧ (l : ℝ) ≤ P.h) (B : ℝ) (hB : 0 ≤ B)
    (hBl : ∀ l ∈ R, Real.log (P.h / (l : ℝ)) ≤ B) :
    ∑ l ∈ R, (1 + max 0 (Real.log (P.h / (l : ℝ)))) * (Real.log (l : ℝ) / (l : ℝ)) ≤
      (1 + B) * ∑ l ∈ R, Real.log (l : ℝ) / (l : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hmax : max 0 (Real.log (P.h / (l : ℝ))) ≤ B := max_le hB (hBl l hl)
  exact mul_le_mul_of_nonneg_right (by linarith) (log_div_prime_nonneg (hR l hl).1)

theorem q_j_bounds {P : Par} {ι : Type} {D : SizeData₂ ι} (hT : D.ShapeT P) {τ : ι} (hτ : τ ∈ D.T2) :
    (D.q τ : ℝ) ≤ P.m ∧ (D.q τ : ℝ) + 2 * (D.j τ : ℝ) ≤ 2 * P.m ∧ (0 : ℝ) ≤ D.q τ ∧
      (0 : ℝ) ≤ D.j τ := by
  obtain ⟨_, _, _, _, _, hqj⟩ := hT τ hτ
  have h1 : (D.q τ : ℝ) + D.j τ ≤ P.m := by exact_mod_cast hqj
  have hq0 : (0 : ℝ) ≤ D.q τ := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ D.j τ := Nat.cast_nonneg _
  exact ⟨by linarith, by linarith, hq0, hj0⟩

private theorem h_add_Nr_bounds_and_log_bounds {P : Par} (H : P.Hyp) (G : P.Large) :
    1 < P.h + (P.Nr : ℝ) ∧ P.h + (P.Nr : ℝ) ≤ 3 * P.b ∧
      0 < Real.log (P.h + (P.Nr : ℝ)) ∧ Real.log (P.h + (P.Nr : ℝ)) ≤ P.L + 11 / 10 := by
  obtain ⟨_, h1, h2, h3, h4⟩ := h_add_Nr_bounds H G
  have d : (1.1 : ℝ) = 11 / 10 := by norm_num
  rw [d] at h4
  exact ⟨h1, h2, h3, h4⟩

private theorem mul_mul_le_mul_mul {a b c a' b' c' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) : a * b * c ≤ a' * b' * c' :=
  mul_le_mul (mul_le_mul ha hb hb0 (ha0.trans ha)) hc hc0
    (mul_nonneg (ha0.trans ha) (hb0.trans hb))

theorem sum_J_mul_log_le_totalBound (rs3 : PrimeCountingBound) {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} [Fintype ι]
    {D : SizeData₂ ι} (I : D.Inputs P) (XC XD : ℝ)
    (hXC : ∀ τ ∈ D.T2, ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime ∧ (l : ℝ) ≤ P.lJ) →
      ∑ l ∈ Q, (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ XC)
    (hXD : ∀ τ ∈ D.T2, ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime ∧ P.lJ < (l : ℝ) ∧ ¬ P.Excl l) →
      ∑ l ∈ Q, min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ) ≤
        XD + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2))
    (Q : Finset ℕ) (hQ : ∀ l ∈ Q, l.Prime) :
    ∑ l ∈ Q, (D.J l : ℝ) * Real.log (l : ℝ) ≤ totalBound P D.T2.card (XC + XD) := by
  have hb' := H.b'_pos
  have hL := G.L_ge
  obtain ⟨A, hAd⟩ : ∃ A : Finset ℕ, A = Q.filter (fun l : ℕ => (l : ℝ) ≤ P.lJ) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : Finset ℕ, B = Q.filter (fun l : ℕ => ¬ (l : ℝ) ≤ P.lJ) := ⟨_, rfl⟩
  obtain ⟨E, hEd⟩ : ∃ E : Finset ℕ, E = B.filter (fun l : ℕ => P.Excl l ∨ l ∈ D.Sp) := ⟨_, rfl⟩
  obtain ⟨W, hWd⟩ : ∃ W : Finset ℕ, W = B.filter (fun l : ℕ => ¬ (P.Excl l ∨ l ∈ D.Sp)) := ⟨_, rfl⟩
  have hQ1 : ∑ l ∈ Q, (D.J l : ℝ) * Real.log (l : ℝ) =
      ∑ l ∈ A, (D.J l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ B, (D.J l : ℝ) * Real.log (l : ℝ) := by
    rw [hAd, hBd, Finset.sum_filter_add_sum_filter_not]
  have hB1 : ∑ l ∈ B, (D.J l : ℝ) * Real.log (l : ℝ) =
      ∑ l ∈ E, (D.J l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (D.J l : ℝ) * Real.log (l : ℝ) := by
    rw [hEd, hWd, Finset.sum_filter_add_sum_filter_not]
  have memA : ∀ l ∈ A, l.Prime ∧ (l : ℝ) ≤ P.lJ := by
    intro l hl
    rw [hAd, Finset.mem_filter] at hl
    exact ⟨hQ l hl.1, hl.2⟩
  have memE : ∀ l ∈ E, l.Prime ∧ P.lJ < (l : ℝ) ∧ (P.Excl l ∨ l ∈ D.Sp) := by
    intro l hl
    rw [hEd, Finset.mem_filter, hBd, Finset.mem_filter] at hl
    exact ⟨hQ l hl.1.1, not_le.1 hl.1.2, hl.2⟩
  have memW : ∀ l ∈ W, l.Prime ∧ P.lJ < (l : ℝ) ∧ ¬ P.Excl l ∧ l ∉ D.Sp := by
    intro l hl
    rw [hWd, Finset.mem_filter, hBd, Finset.mem_filter] at hl
    push_neg at hl
    exact ⟨hQ l hl.1.1, hl.1.2, hl.2.1, hl.2.2⟩
  have hdisj : Disjoint A W := by
    rw [Finset.disjoint_left]
    intro l ha hw
    have h1 := (memA l ha).2
    have h2 := (memW l hw).2.1
    linarith
  have hfNL : 0 ≤ (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L := mul_nonneg (by positivity) (by linarith)
  have bE : ∑ l ∈ E, (D.J l : ℝ) * Real.log (l : ℝ) ≤ (E.card : ℝ) * ((P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L) := by
    calc ∑ l ∈ E, (D.J l : ℝ) * Real.log (l : ℝ) ≤ ∑ _l ∈ E, (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L := by
          apply Finset.sum_le_sum
          intro l hl
          obtain ⟨hp, _, hES⟩ := memE l hl
          have hJ : (D.J l : ℝ) ≤ ∑ τ, (D.ex τ l : ℝ) := by
            exact_mod_cast I.boundA l hp (Or.inr hES)
          exact (mul_le_mul_of_nonneg_right hJ (log_prime_nonneg hp)).trans
            (costBound_holds P H G ι D I.card_ι I.thinA I.thickA I.widths l hp)
      _ = (E.card : ℝ) * ((P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hEsub : E ⊆ E.filter (fun l : ℕ => P.Excl l) ∪ D.Sp := by
    intro l hl
    rw [Finset.mem_union, Finset.mem_filter]
    rcases (memE l hl).2.2 with h | h
    · exact Or.inl ⟨hl, h⟩
    · exact Or.inr h
  have hEcard : E.card ≤ (E.filter (fun l : ℕ => P.Excl l)).card + D.Sp.card :=
    (Finset.card_le_card hEsub).trans (Finset.card_union_le _ _)
  have hEx := exceptionalCount_holds P H G (E.filter (fun l : ℕ => P.Excl l)) (fun l hl => by
    rw [Finset.mem_filter] at hl
    exact ⟨(memE l hl.1).1, (memE l hl.1).2.1, hl.2⟩)
  have hEcardR : (E.card : ℝ) ≤ P.S + P.η + (P.t : ℝ) + 2 * (P.kmax : ℝ) + 6 := by
    have h1 : (E.card : ℝ) ≤ ((E.filter (fun l : ℕ => P.Excl l)).card : ℝ) + (D.Sp.card : ℝ) := by
      exact_mod_cast hEcard
    have h2 : (D.Sp.card : ℝ) ≤ 5 := by exact_mod_cast I.card_Sp
    linarith
  have bE' := mul_le_mul_of_nonneg_right hEcardR hfNL
  have hAW : ∑ l ∈ A, (D.J l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (D.J l : ℝ) * Real.log (l : ℝ) ≤
      ∑ τ : ι, (∑ l ∈ A, (D.ex τ l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ)) := by
    calc ∑ l ∈ A, (D.J l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (D.J l : ℝ) * Real.log (l : ℝ)
        ≤ ∑ l ∈ A, ∑ τ : ι, (D.ex τ l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, ∑ τ : ι, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ) := by
          apply add_le_add
          · apply Finset.sum_le_sum
            intro l hl
            obtain ⟨hp, hle⟩ := memA l hl
            have hJ : (D.J l : ℝ) ≤ ∑ τ, (D.ex τ l : ℝ) := by
              exact_mod_cast I.boundA l hp (Or.inl hle)
            rw [← Finset.sum_mul]
            exact mul_le_mul_of_nonneg_right hJ (log_prime_nonneg hp)
          · apply Finset.sum_le_sum
            intro l hl
            obtain ⟨hp, hlt, hEx', hSp⟩ := memW l hl
            obtain ⟨_, _, _, h4, _, h6, _, h8⟩ := paramsLargePrime_holds P H G l hlt
            have hJ := I.boundW l hp hlt hEx' hSp h8 h6 h4
            rw [← Finset.sum_mul]
            exact mul_le_mul_of_nonneg_right hJ (log_prime_nonneg hp)
      _ = ∑ τ : ι, ∑ l ∈ A, (D.ex τ l : ℝ) * Real.log (l : ℝ) + ∑ τ : ι, ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ) := by
          congr 1 <;> exact Finset.sum_comm
      _ = ∑ τ : ι, (∑ l ∈ A, (D.ex τ l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ)) :=
          (Finset.sum_add_distrib).symm
  have top_degree_le_two_b : ∀ τ ∈ D.T2, (∑ l ∈ A, (D.ex τ l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ)) ≤
      XC + (XD + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2)) := by
    intro τ hτ
    have e : ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ) = ∑ l ∈ W, min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ) :=
      Finset.sum_congr rfl (fun l _ => by rw [if_pos hτ])
    rw [e]
    exact add_le_add (hXC τ hτ A memA)
      (hXD τ hτ W (fun l hl => ⟨(memW l hl).1, (memW l hl).2.1, (memW l hl).2.2.1⟩))
  have bN : ∀ τ, τ ∉ D.T2 → (∑ l ∈ A, (D.ex τ l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ)) ≤
      1.3 * (P.Nr : ℝ) ^ 2 * P.b' := by
    intro τ hτ
    have e : ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ) = ∑ l ∈ W, (D.ex τ l : ℝ) * Real.log (l : ℝ) :=
      Finset.sum_congr rfl (fun l _ => by rw [if_neg hτ])
    rw [e, ← Finset.sum_union hdisj]
    refine thinSum_holds rs3 P H G ι D I.thinA I.widths τ hτ (A ∪ W) (fun l hl => ?_)
    rcases Finset.mem_union.1 hl with h | h
    · exact (memA l h).1
    · exact (memW l h).1
  have hY0 : 0 ≤ 1.3 * (P.Nr : ℝ) ^ 2 * P.b' := mul_nonneg (by positivity) hb'.le
  have hF : Finset.univ.filter (fun τ => τ ∈ D.T2) = D.T2 := by
    ext τ
    simp
  have hcard2 : (Finset.univ.filter (fun τ => ¬ τ ∈ D.T2)).card ≤ P.f := by
    rw [← I.card_ι]
    exact Finset.card_le_univ _
  have hcard2R : ((Finset.univ.filter (fun τ => ¬ τ ∈ D.T2)).card : ℝ) ≤ P.f := by
    exact_mod_cast hcard2
  have hsumτ : ∑ τ : ι, (∑ l ∈ A, (D.ex τ l : ℝ) * Real.log (l : ℝ) + ∑ l ∈ W, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ)) * Real.log (l : ℝ)) ≤
      (D.T2.card : ℝ) * (XC + (XD + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2)))
        + (P.f : ℝ) * (1.3 * (P.Nr : ℝ) ^ 2 * P.b') := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ => τ ∈ D.T2)]
    refine le_trans (add_le_add (Finset.sum_le_sum (fun τ hτ => top_degree_le_two_b τ (Finset.mem_filter.1 hτ).2))
      (Finset.sum_le_sum (fun τ hτ => bN τ (Finset.mem_filter.1 hτ).2))) ?_
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hF]
    nlinarith [mul_le_mul_of_nonneg_right hcard2R hY0]
  rw [hQ1, hB1]
  unfold totalBound
  linarith

theorem totalBound_mono (P : Par) (T : ℕ) {X Y : ℝ} (h : X ≤ Y) : totalBound P T X ≤ totalBound P T Y := by
  unfold totalBound
  have := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
  linarith

private theorem log_four_le' : Real.log 4 ≤ 139 / 100 := by
  have e : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have := Real.log_two_lt_d9
  norm_num at this
  linarith

theorem pr_eq_primesUpTo_floor (y : ℝ) : pr y = Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo ⌊y⌋₊ := rfl

theorem chebyshevThetaElementary_holds : ConvolutionKernelIntegrable := by
  intro y hy
  rw [pr_eq_primesUpTo_floor]
  have h := Formalism.RankGapBounds.ChebyshevFactorialBounds.chebyshevThetaLe_holds ⌊y⌋₊
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  exact h.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hy) h4)

theorem sum_div_mul_log_le_log_factorial' (n : ℕ) :
    ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ) ≤
      Real.log ((n.factorial : ℕ) : ℝ) := by
  have hfac : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hprod := Nat.prod_pow_prime_padicValNat (n.factorial) hfac (n.factorial + 1) (Nat.lt_succ_self _)
  have hlog : Real.log ((n.factorial : ℕ) : ℝ) =
      ∑ p ∈ (Finset.range (n.factorial + 1)).filter Nat.Prime,
        (padicValNat p n.factorial : ℝ) * Real.log (p : ℝ) := by
    have h := congrArg (fun x : ℕ => Real.log (x : ℝ)) hprod
    simp only [Nat.cast_prod, Nat.cast_pow] at h
    rw [Real.log_prod (fun p hp => pow_ne_zero _
      (Nat.cast_ne_zero.2 (Finset.mem_filter.1 hp).2.ne_zero))] at h
    simp only [Real.log_pow] at h
    exact h.symm
  rw [hlog]
  calc ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ)
      ≤ ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, (padicValNat p n.factorial : ℝ) * Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' : p.Prime := (Finset.mem_filter.1 hp).2
        have := Fact.mk hp'
        have hv : n / p ≤ padicValNat p n.factorial := by
          rw [padicValNat_factorial (b := max 2 (Nat.log p n + 1))
            (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))]
          calc n / p = n / p ^ 1 := by rw [pow_one]
            _ ≤ ∑ i ∈ Finset.Ico 1 (max 2 (Nat.log p n + 1)), n / p ^ i :=
                Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _)
                  (Finset.mem_Ico.2 ⟨le_rfl, lt_of_lt_of_le (by norm_num) (le_max_left _ _)⟩)
        have hv' : ((n / p : ℕ) : ℝ) ≤ (padicValNat p n.factorial : ℝ) := by exact_mod_cast hv
        exact mul_le_mul_of_nonneg_right hv' (log_prime_nonneg hp')
    _ ≤ ∑ p ∈ (Finset.range (n.factorial + 1)).filter Nat.Prime,
        (padicValNat p n.factorial : ℝ) * Real.log (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo, Finset.mem_filter, Finset.mem_range] at hp ⊢
          exact ⟨lt_of_lt_of_le hp.1 (Nat.succ_le_succ (Nat.self_le_factorial n)), hp.2⟩
        · intro p hp _
          have hp' : p.Prime := (Finset.mem_filter.1 hp).2
          exact mul_nonneg (Nat.cast_nonneg _) (log_prime_nonneg hp')

theorem sum_log_div_le_log_add_log_four (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, Real.log (p : ℝ) / (p : ℝ) ≤
      Real.log (n : ℝ) + Real.log 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : Real.log ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    have h1 : ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have h2 : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
    calc Real.log ((n.factorial : ℕ) : ℝ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log h2 h1
      _ = (n : ℝ) * Real.log (n : ℝ) := Real.log_pow _ _
  have key : (n : ℝ) * ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, Real.log (p : ℝ) / (p : ℝ) ≤
      (n : ℝ) * (Real.log (n : ℝ) + Real.log 4) := by
    calc (n : ℝ) * ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, Real.log (p : ℝ) / (p : ℝ)
        = ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, (n : ℝ) / (p : ℝ) * Real.log (p : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          ring
      _ ≤ ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, (((n / p : ℕ) : ℝ) + 1) * Real.log (p : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          have hp' : p.Prime := (Finset.mem_filter.1 hp).2
          have h1 := Nat.lt_floor_add_one ((n : ℝ) / (p : ℝ))
          rw [Nat.floor_div_eq_div] at h1
          exact mul_le_mul_of_nonneg_right h1.le (log_prime_nonneg hp')
      _ = ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ)
          + ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, Real.log (p : ℝ) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p _
          ring
      _ ≤ Real.log ((n.factorial : ℕ) : ℝ) + Real.log 4 * (n : ℝ) :=
          add_le_add (sum_div_mul_log_le_log_factorial' n) (Formalism.RankGapBounds.ChebyshevFactorialBounds.chebyshevThetaLe_holds n)
      _ ≤ (n : ℝ) * (Real.log (n : ℝ) + Real.log 4) := by linarith
  exact le_of_mul_le_mul_left key hn0

theorem mertensLogElementary_holds : MertensLogElementary := by
  intro y hy
  rw [pr_eq_primesUpTo_floor]
  have hn : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact hy)
  have h := sum_log_div_le_log_add_log_four ⌊y⌋₊ hn
  have h1 : (1 : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hn
  have h2 := Real.log_le_log (by linarith) (Nat.floor_le (by linarith : (0 : ℝ) ≤ y))
  linarith

theorem mertensReciprocalElementary_holds : MertensReciprocalElementary := by
  intro y hy
  rw [pr_eq_primesUpTo_floor]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊y⌋₊ := ⟨_, rfl⟩
  rw [← hn]
  have hn1 : 1 ≤ n := by rw [hn]; exact Nat.le_floor (by rw [Nat.cast_one]; exact hy)
  have hsub : Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n ⊆ (Finset.Icc 1 n).erase 1 := by
    intro p hp
    simp only [Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo, Finset.mem_filter, Finset.mem_range] at hp
    rw [Finset.mem_erase, Finset.mem_Icc]
    exact ⟨hp.2.one_lt.ne', hp.2.one_lt.le, by omega⟩
  have s1 : ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, (1 : ℝ) / (p : ℝ) ≤
      ∑ i ∈ (Finset.Icc 1 n).erase 1, (1 : ℝ) / (i : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  have s2 := Finset.add_sum_erase (Finset.Icc 1 n) (fun i : ℕ => (1 : ℝ) / (i : ℝ))
    (Finset.mem_Icc.2 ⟨le_rfl, hn1⟩)
  simp only [Nat.cast_one, div_one] at s2
  have s3 := Formalism.CohomologicalDescent.sums_harmonic_real n
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have s4 : Real.log (n : ℝ) ≤ Real.log y := Real.log_le_log (by linarith)
    (by rw [hn]; exact Nat.floor_le (by linarith))
  linarith

theorem smallPrimeSumElementary_holds : SumCE := by
  intro P H G ι D hA τ hτ Q hQ
  have hb := b_pos' P
  have hL := G.L_ge
  have h8 := eight_lt_lJ H G
  obtain ⟨hlg1, hlg2⟩ := log_lJ_bounds H G
  have hmbL : 0 ≤ 2 * (P.m : ℝ) * P.b * P.L :=
    mul_nonneg (mul_nonneg (by positivity) hb.le) (by linarith)
  have hsub : Q ⊆ pr P.lJ := subset_primesLe (by linarith) hQ
  have s1 : ∑ l ∈ Q, (1 : ℝ) / (l : ℝ) ≤ ∑ p ∈ pr P.lJ, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have s2 := mertensReciprocalElementary_holds P.lJ (by linarith)
  have hsum : ∑ l ∈ Q, (1 : ℝ) / (l : ℝ) ≤ P.L := by linarith
  calc ∑ l ∈ Q, (D.ex τ l : ℝ) * Real.log (l : ℝ)
      ≤ ∑ l ∈ Q, 2 * (P.m : ℝ) * P.b * P.L / (l : ℝ) :=
        Finset.sum_le_sum (fun l hl => thickTerm_holds P H G ι D hA τ hτ l (hQ l hl).1 (hQ l hl).2)
    _ = 2 * (P.m : ℝ) * P.b * P.L * ∑ l ∈ Q, (1 : ℝ) / (l : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
    _ ≤ 2 * (P.m : ℝ) * P.b * P.L * P.L := mul_le_mul_of_nonneg_left hsum hmbL
    _ = 2 * (P.m : ℝ) * P.b * P.L ^ 2 := by ring

theorem small_terms_le_of_log_four {P : Par} (H : P.Hyp) (G : P.Large) (s3 s4 : ℝ)
    (h3 : s3 ≤ Real.log (P.h + (P.Nr : ℝ)) + Real.log 4) (h4 : s4 ≤ (P.S + 1) * Real.log P.h) :
    (P.k : ℝ) * P.S * s3 + (P.k : ℝ) * s4 ≤ 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2) := by
  have hk0 : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  have hS := H.S_nonneg
  obtain ⟨_, _, _, hl1⟩ := h_add_Nr_bounds_and_log_bounds H G
  obtain ⟨c1, c2⟩ := log_h_pos_and_le H G
  have h4' := log_four_le'
  have hL := G.L_ge
  have a1 : (P.k : ℝ) * P.S * s3 ≤ (P.k : ℝ) * P.S * (P.L + 249 / 100) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hk0 hS)
  have a2 : (P.k : ℝ) * s4 ≤ (P.k : ℝ) * ((P.S + 1) * (P.L + 7 / 10)) :=
    mul_le_mul_of_nonneg_left (h4.trans (mul_le_mul_of_nonneg_left c2 (by linarith))) hk0
  nlinarith [mul_nonneg hk0 (show (0 : ℝ) ≤ 81 / 100 * P.S + P.L + 33 / 10 by linarith)]

theorem largePrimeSumElementary_holds : SumDE := by
  intro P H G ι D hA hC hT hNW τ hτ Q hQ
  have hb := b_pos' P
  have hL := G.L_ge
  have hsplit := sum_min_cW_le_split H G hA hC hNW hτ hQ
  set R := Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h) with hRdef
  have hR : ∀ l ∈ R, l.Prime ∧ P.lJ < (l : ℝ) ∧ (l : ℝ) ≤ P.h := by
    intro l hl
    rw [hRdef, Finset.mem_filter] at hl
    exact ⟨(hQ l hl.1).1, (hQ l hl.1).2.1, hl.2⟩
  have hJ8 := eight_lt_lJ H G
  obtain ⟨c1, c2⟩ := log_h_pos_and_le H G
  have hh := (paramsBasic_holds P H G).2.2
  have h7 := b_add_seven_le_h H
  obtain ⟨hq, hqj, hq0, hj0⟩ := q_j_bounds hT hτ
  obtain ⟨n1, n2, n3, n4⟩ := h_add_Nr_bounds_and_log_bounds H G
  have z1 : 0 ≤ ∑ l ∈ R, Real.log (l : ℝ) / ((l : ℝ) - 1) := Finset.sum_nonneg (fun l hl => by
    have hl2 := two_le_prime_cast (hR l hl).1
    exact div_nonneg (log_prime_nonneg (hR l hl).1) (by linarith))
  have z2 : 0 ≤ ∑ l ∈ R, Real.log (l : ℝ) :=
    Finset.sum_nonneg (fun l hl => log_prime_nonneg (hR l hl).1)
  have z3 : 0 ≤ ∑ l ∈ R, Real.log (l : ℝ) / (l : ℝ) :=
    Finset.sum_nonneg (fun l hl => log_div_prime_nonneg (hR l hl).1)
  have z6 : 0 ≤ ∑ l ∈ R, (1 + max 0 (Real.log (P.h / (l : ℝ)))) * (Real.log (l : ℝ) / (l : ℝ)) :=
    Finset.sum_nonneg (fun l hl => mul_nonneg
      (by have := le_max_left (0 : ℝ) (Real.log (P.h / (l : ℝ))); linarith)
      (log_div_prime_nonneg (hR l hl).1))
  have hm0 : (0 : ℝ) ≤ P.m := Nat.cast_nonneg _
  have hm2b : (0 : ℝ) ≤ P.m * (2 * P.b) := mul_nonneg hm0 (by linarith)
  have hmb : 0 ≤ (P.m : ℝ) * P.b := mul_nonneg hm0 hb.le
  have hmbL : 0 ≤ (P.m : ℝ) * P.b * P.L := mul_nonneg hmb (by linarith)
  have u1 : (D.q τ : ℝ) * P.h ≤ P.m * (2 * P.b) := mul_le_mul hq hh (by linarith) hm0
  have pred : ∑ l ∈ R, Real.log (l : ℝ) / ((l : ℝ) - 1) ≤
      9 / 8 * ∑ l ∈ R, Real.log (l : ℝ) / (l : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    obtain ⟨hp, hlt, _⟩ := hR l hl
    have h8' : 8 < l := by exact_mod_cast (show (8 : ℝ) < l by linarith)
    have h9 : (9 : ℝ) ≤ l := by exact_mod_cast (show 9 ≤ l by omega)
    have hl0 : (l : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have e : Real.log (l : ℝ) / (l : ℝ) * ((l : ℝ) / ((l : ℝ) - 1)) = Real.log (l : ℝ) / ((l : ℝ) - 1) := by
      rw [div_mul_div_comm, mul_comm (Real.log (l : ℝ)) (l : ℝ), mul_div_mul_left _ _ hl0]
    have hq98 : (l : ℝ) / ((l : ℝ) - 1) ≤ 9 / 8 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    rw [← e]
    have := mul_le_mul_of_nonneg_left hq98 (log_div_prime_nonneg hp)
    linarith
  have hNr0 : (0 : ℝ) ≤ P.Nr := Nat.cast_nonneg _
  have hsub := subset_primesLe_h_add_Nr H G hR
  have s2 : ∑ l ∈ R, Real.log (l : ℝ) ≤ Real.log 4 * (P.h + (P.Nr : ℝ)) := by
    have a := chebyshevThetaElementary_holds (P.h + (P.Nr : ℝ)) (by linarith)
    have b : ∑ l ∈ R, Real.log (l : ℝ) ≤ ∑ p ∈ pr (P.h + (P.Nr : ℝ)), Real.log (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => log_prime_nonneg (prime_of_mem_primesLe hp))
    linarith
  have s3 : ∑ l ∈ R, Real.log (l : ℝ) / (l : ℝ) ≤ Real.log (P.h + (P.Nr : ℝ)) + Real.log 4 := by
    have a := mertensLogElementary_holds (P.h + (P.Nr : ℝ)) (by linarith)
    have b : ∑ l ∈ R, Real.log (l : ℝ) / (l : ℝ) ≤ ∑ p ∈ pr (P.h + (P.Nr : ℝ)), Real.log (p : ℝ) / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => log_div_prime_nonneg (prime_of_mem_primesLe hp))
    linarith
  have s4 := sum_residueIndicator_mul_log_le H G hT hτ hR
  have s5 := sum_gateTerm_mul_log_le H G hT hτ hR
  have st := small_terms_le_of_log_four H G _ _ s3 s4
  have h4 := log_four_le'
  have h40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hA3 : ∑ l ∈ R, Real.log (l : ℝ) / (l : ℝ) ≤ P.L + 249 / 100 := by linarith
  have hA2 : ∑ l ∈ R, Real.log (l : ℝ) ≤ 139 / 100 * (3 * P.b) := by
    have := mul_le_mul h4 n2 (by linarith) (by norm_num)
    linarith
  have hBl : ∀ l ∈ R, Real.log (P.h / (l : ℝ)) ≤ P.L + 7 / 10 := by
    intro l hl
    have hl2 := two_le_prime_cast (hR l hl).1
    have : Real.log (P.h / (l : ℝ)) ≤ Real.log P.h :=
      Real.log_le_log (div_pos (by linarith) (by linarith)) (div_le_self (by linarith) (by linarith))
    linarith
  have s6 := sum_one_add_log_div_le hR (P.L + 7 / 10) (by linarith) hBl
  have t1 := mul_mul_le_mul_mul hqj n2 (pred.trans (mul_le_mul_of_nonneg_left hA3 (by norm_num)))
    (by linarith) (by linarith) z1
  have t2 : 6 * ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * ∑ l ∈ R, Real.log (l : ℝ)
      ≤ 6 * (2 * (P.m : ℝ)) * (139 / 100 * (3 * P.b)) :=
    mul_le_mul (by linarith) hA2 z2 (by linarith)
  have u2 : (1 + Real.log P.h) * Real.log P.h ≤ (P.L + 17 / 10) * (P.L + 7 / 10) :=
    mul_le_mul (by linarith) c2 c1.le (by linarith)
  have u3 := mul_le_mul u1 u2 (mul_nonneg (by linarith) c1.le) hm2b
  have u4 := mul_le_mul_of_nonneg_left hA3 (by linarith : (0 : ℝ) ≤ 1 + (P.L + 7 / 10))
  have u5 := mul_le_mul u1 (s6.trans u4) z6 hm2b
  have d25 : (2.5 : ℝ) = 5 / 2 := by norm_num
  rw [d25]
  constructor
  · linarith
  · have hq14 : (0 : ℝ) ≤ 14 * (P.L - 4) ^ 2 + 83 * (P.L - 4) + 9 := by nlinarith
    linarith [mul_nonneg hmb hq14]

theorem totalElementary_holds : TotalElementary := by
  intro rs3 P H G ι _ D I hNW Q hQ
  have hXC : ∀ τ ∈ D.T2, ∀ Q' : Finset ℕ, (∀ l ∈ Q', l.Prime ∧ (l : ℝ) ≤ P.lJ) →
      ∑ l ∈ Q', (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ 2 * (P.m : ℝ) * P.b * P.L ^ 2 :=
    fun τ hτ Q' hQ' => smallPrimeSumElementary_holds P H G ι D I.thickA τ hτ Q' hQ'
  have hXD : ∀ τ ∈ D.T2, ∀ Q' : Finset ℕ, (∀ l ∈ Q', l.Prime ∧ P.lJ < (l : ℝ) ∧ ¬ P.Excl l) →
      ∑ l ∈ Q', min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ) ≤
        18 * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2) := by
    intro τ hτ Q' hQ'
    have h := largePrimeSumElementary_holds P H G ι D I.thickA I.cloudA I.shapeT hNW τ hτ Q' hQ'
    exact h.1.trans h.2
  refine (sum_J_mul_log_le_totalBound rs3 H G I _ _ hXC hXD Q hQ).trans (totalBound_mono P _ ?_)
  have hmbL : 0 ≤ (P.m : ℝ) * P.b * P.L ^ 2 :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (b_pos' P).le) (sq_nonneg _)
  linarith

end Formalism.CohomologicalDescent.LogSmallConstantBounds
