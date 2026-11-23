import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterPrecisionLeLengthAndRank

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.WtShape

section Rec

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P)

theorem six_le_r (R : Ranks) : 6 ≤ R.r := by
  have := R.two_le_m; have := R.m_add_three_le_k; unfold Ranks.r; omega

theorem one_le_Dp : 1 ≤ T.Dp := by
  rw [T.Dp_eq]
  have h2 : 0 < D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  exact Nat.mul_pos h2 (Nat.choose_pos (by have := six_le_r D.R; omega))

theorem forty_le_PP : 40 ≤ T.PP := le_trans (by exact_mod_cast T.nW_40) T.nW_le

theorem len_ge : 4 * T.Dp + 4 ≤ ⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ := by
  have h1 : (1 : ℝ) ≤ T.Dp := by exact_mod_cast one_le_Dp T
  have h2 := forty_le_PP T
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 0 < D.R.m)
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : D.R.m ≤ D.R.k)
  have h3 : T.PP ^ 2 * (T.Dp : ℝ) ^ 2 ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
    rw [le_div_iff₀ hm]; exact mul_le_mul_of_nonneg_left hmk (by positivity)
  have h4 : (8 : ℝ) * (T.Dp : ℝ) ^ 2 ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have h5 : ((4 * T.Dp + 4 : ℕ) : ℝ) ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
    push_cast; nlinarith
  exact_mod_cast h5.trans (Nat.le_ceil _)

theorem cZeroN_le_TO (j : ℕ) : cZeroN D j ≤ 12 * T.TO := by
  have h1 := cZeroN_le D j
  have h2 := T.TO_11D2
  have h6 := six_le_r D.R
  have h3 : D.R.r ^ 4 ≤ 6 * (D.R.r.choose 2) ^ 2 := by
    obtain ⟨s, hs⟩ : ∃ s, D.R.r = s + 1 := ⟨D.R.r - 1, by omega⟩
    have e : 2 * (D.R.r.choose 2) = D.R.r * s := by
      rw [hs, Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_div_cancel' (by
        rw [mul_comm]; exact (Nat.even_mul_succ_self s).two_dvd)]
    have e2 : 4 * (D.R.r.choose 2) ^ 2 = D.R.r ^ 2 * s ^ 2 := by
      rw [← mul_pow, ← e]; ring
    have e3 : 4 * D.R.r ^ 2 ≤ 6 * s ^ 2 := by
      have : 5 ≤ s := by omega
      rw [hs]; nlinarith
    have e4 : D.R.r ^ 2 * (4 * D.R.r ^ 2) ≤ D.R.r ^ 2 * (6 * s ^ 2) := Nat.mul_le_mul_left _ e3
    nlinarith
  have h4 : D.R.f ^ 2 * D.R.r ^ 4 ≤ D.R.f ^ 2 * (6 * (D.R.r.choose 2) ^ 2) := Nat.mul_le_mul_left _ h3
  rw [T.Dp_eq, mul_pow] at h2
  nlinarith

theorem spacing_ge (j n : ℕ) (hn : n ≤ T.TO) :
    4 * ((cZeroN D j : ℝ) + 2 * D.R.r + n + T.Dp + 1) ≤ LevelStarExponents.h0 L ∧ 24 * (D.R.r : ℝ) * n ≤ LevelStarExponents.h0 L ∧
      4 * (n : ℝ) ^ 2 ≤ LevelStarExponents.h0 L := by
  have a1 : (cZeroN D j : ℝ) ≤ 12 * T.TO := by exact_mod_cast cZeroN_le_TO T j
  have a2 : 6 * (D.R.r : ℝ) ≤ T.TO := by
    have h := T.order_ge_rank_bound
    have : 6 * D.R.r ≤ T.TO := by nlinarith [Nat.zero_le (D.R.r * T.Dp)]
    exact_mod_cast this
  have a3 : 40 * ((T.Dp : ℝ) + 2) ≤ T.TO := by exact_mod_cast T.TO_40
  have a4 : (n : ℝ) ≤ T.TO := by exact_mod_cast hn
  have a5 := T.heightBound_ge_order_sq
  have b0 : (0 : ℝ) ≤ T.Dp := Nat.cast_nonneg _
  have b1 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have b2 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have b3 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨by nlinarith, ?_, by nlinarith⟩
  have : 6 * (D.R.r : ℝ) * n ≤ T.TO * T.TO := mul_le_mul a2 a4 b2 (by linarith)
  nlinarith

theorem prod_bounds (n : ℕ) (hn : n ≤ T.TO) :
    T.PP * n * D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * T.Dp ≤ LevelStarExponents.h0 L ∧
    T.PP ^ 2 * D.R.r * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3 ≤ L.sc.b ∧
    T.PP * n * (T.Dp : ℝ) ^ 2 * L.sc.L ≤ L.sc.b := by
  have a4 : (n : ℝ) ≤ T.TO := by exact_mod_cast hn
  have hP := forty_le_PP T
  have hP0 : 0 ≤ T.PP := by linarith
  have hrN : (D.R.r : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have : D.R.r ≤ D.R.N D.R.m := by
      unfold Ranks.r Ranks.N
      have h1 : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      omega
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans ?_ T.heightBound_ge_order_product
    have e1 : T.PP * n * (D.R.r : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) ≤
        T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) := by
      gcongr
    have e2 : T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) ≤
        T.ChT * (T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k *
          (T.Dp : ℝ)) := le_mul_of_one_le_left (by positivity) T.ChT_ge
    calc _ ≤ _ := e1.trans e2
      _ = _ := by ring
  · refine le_trans ?_ T.b_ge
    have e2 : T.PP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3 ≤
        T.CbN * (T.PP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3) :=
      le_mul_of_one_le_left (by positivity) T.CbN_ge
    calc _ ≤ _ := e2
      _ = _ := by ring
  · have hb0 : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
    have hlb : Real.log L.sc.b = L.sc.L := by unfold Scale.b; exact Real.log_exp _
    have hL : 0 ≤ L.sc.L := by unfold Scale.L; exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
    have c1 := T.TD2'
    have c2 := T.TO_PP'
    rw [hlb] at c1
    have c3 : (1 : ℝ) ≤ T.TO := by
      have := T.TO_40
      exact_mod_cast (by omega : 1 ≤ T.TO)
    have c4 : T.PP ≤ L.sc.b ^ (1 / 2 : ℝ) := le_trans (le_mul_of_one_le_left hP0 c3) c2
    have c5 : (n : ℝ) * (T.Dp : ℝ) ^ 2 * L.sc.L ≤ L.sc.b ^ (1 / 2 : ℝ) := le_trans (by gcongr) c1
    have c6 : L.sc.b ^ (1 / 2 : ℝ) * L.sc.b ^ (1 / 2 : ℝ) = L.sc.b := by
      rw [← Real.rpow_add hb0]; norm_num
    calc _ = T.PP * ((n : ℝ) * (T.Dp : ℝ) ^ 2 * L.sc.L) := by ring
      _ ≤ _ := mul_le_mul c4 c5 (by positivity) (by positivity)
      _ = _ := c6

theorem abs_logOm_le (hS : SizesAt L) (hL : 3 ≤ L.sc.L) : |L.logOm| ≤ 3 * L.sc.L := by
  obtain ⟨-, -, -, -, -, hCond, hQD, -⟩ := hS
  have hx0 : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have h1 := log_rdE_le_L D L hCond hQD
  have hrd : 1 ≤ D.host.rdE := hQD.2.2.2.2.2.2.1
  have h0 := Real.log_nonneg hrd
  have h2 : |L.logDerivativeAtOne| ≤ L.sc.L := hQD.2.2.2.2.2.1
  have h3 := Real.one_half_lt_eulerMascheroniConstant
  have h4 := Real.eulerMascheroniConstant_lt_two_thirds
  have h5 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h6 : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos; linarith [Real.pi_le_four]
  have h7 := Real.log_two_lt_d9
  have h8 := Real.log_two_gt_d9
  unfold SizeData₂.logOm Host.v
  rw [Real.log_div Real.pi_pos.ne' (by positivity), Real.log_div (by positivity) (by norm_num)]
  obtain ⟨h9, h10⟩ := abs_le.1 h2
  rw [abs_le]
  constructor <;> linarith

def entR (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) : ℝ :=
  sgR D t n + DV.wSz D ((i : ℕ) + 1) t + n - ((D.R.k : ℝ) + i) + ((D.R.r : ℝ) + 1) / 2 -
    if n < D.R.k + i then 0 else (D.R.r : ℝ)

theorem ent_cast (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) : ((ent D i t n : ℚ) : ℝ) = entR D i t n := by
  unfold ent entR sgR
  rw [← DV.eQ_cast, eQ_succ]
  split_ifs <;> push_cast <;> ring

theorem entR_cloud (L : SizeData₂ D) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) (hn : n < D.R.k - 1) :
    DV.wSz D ((i : ℕ) + 1) t - D.R.r ≤ entR D i t n ∧ entR D i t n ≤ DV.wSz D ((i : ℕ) + 1) t + L.Sc + D.R.r := by
  unfold entR
  rw [if_pos (by omega), sgR_cloud D t n hn]
  obtain ⟨v0, v1⟩ := L.cloud_v t ⟨n, hn⟩
  have c1 : (n : ℝ) + 2 ≤ D.R.k := by exact_mod_cast (by omega : n + 2 ≤ D.R.k)
  have c3 : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast i.2
  have c4 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have c5 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have c6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast six_le_r D.R
  have := r_cast D.R
  constructor <;> linarith

theorem entR_node (L : SizeData₂ D) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) (hn : D.R.k - 1 ≤ n) (hr : n < D.R.r) :
    |entR D i t n| ≤ L.etaSz + D.R.r := by
  obtain ⟨a1, a2⟩ := abs_le.1 (sgR_be D L ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 t n hn hr)
  have c1 : (D.R.k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (by omega : D.R.k ≤ n + 1)
  have c2 : (n : ℝ) + 1 ≤ D.R.r := by exact_mod_cast hr
  have c3 : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast i.2
  have c5 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have c7 : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  have := r_cast D.R
  unfold entR
  split_ifs with h
  · have c8 : (n : ℝ) + 1 ≤ (D.R.k : ℝ) + (i : ℕ) := by exact_mod_cast h
    rw [abs_le]; constructor <;> linarith
  · have c8 : (D.R.k : ℝ) + (i : ℕ) ≤ n := by exact_mod_cast not_lt.1 h
    rw [abs_le]; constructor <;> linarith

theorem entR_step (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) :
    entR D i t n - entR D i t (n + 1) =
      sgR D t n - sgR D t (n + 1) - 1 + if n + 1 = D.R.k + i then (D.R.r : ℝ) else 0 := by
  unfold entR
  split_ifs <;> first | omega | (push_cast; ring)

theorem entR_cloud_sub (L : SizeData₂ D) (i : Fin D.R.m) (t : D.what₂.Tau)
    (hs : ∀ a, a + 1 < D.R.r → 1 ≤ sgR D t a - sgR D t (a + 1)) (n : ℕ) (hn : n < D.R.k - 1) :
    0 ≤ entR D i t n - entR D i t (D.R.k - 1 - 1) ∧ entR D i t n - entR D i t (D.R.k - 1 - 1) ≤ L.Sc := by
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have h1 := steps_sum (sgR D t) 0 D.R.r 1 (fun a _ ha => hs a ha) n (Nat.zero_le _) (D.R.k - 1 - 1) (by omega) (by omega)
  have h2 : (n : ℝ) ≤ ((D.R.k - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ D.R.k - 1 - 1)
  have h3 := (L.cloud_v t ⟨n, hn⟩).2
  have h4 := (L.cloud_v t ⟨D.R.k - 1 - 1, by omega⟩).1
  rw [← sgR_cloud] at h3 h4
  unfold entR
  rw [if_pos (by omega), if_pos (by omega)]
  constructor <;> linarith

end Rec

end GlobalTheory.CovTop.WtShape

end
