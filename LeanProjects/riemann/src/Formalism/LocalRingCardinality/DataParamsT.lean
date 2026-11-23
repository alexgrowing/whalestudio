import Formalism.LocalRingCardinality.DataParams

noncomputable section

namespace Formalism.BasicNotions

open NumberField LevelStarExponents

def logdE (D : D7) : ℝ := Real.log |((discr D.host.E : ℤ) : ℝ)|

def zBase {D : D7} (L : SizeData₂ D) : ℝ := (D.R.f : ℝ) * (D.R.r : ℝ) * L.sc.L

structure ParamsT (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) : Type where

  TO : ℕ

  nWn : ℕ

  nP : ℕ

  PP : ℝ

  Dp : ℕ

  s : ℕ

  CP : ℝ
  one_le_CP : 1 ≤ CP

  eP : ℝ
  eP_ge : 12 ≤ eP

  Cp : ℝ
  Cp_ge : 1 ≤ Cp

  Cb : ℝ
  Cb_nonneg : 0 ≤ Cb

  cTO : ℝ

  ChT : ℝ
  ChT_ge : 1 ≤ ChT

  CbN : ℝ
  CbN_ge : 1 ≤ CbN

  PP_eq : PP = CP * zBase L ^ eP

  Dp_eq : Dp = D.R.f * D.R.r.choose 2

  PP_poly : PP ≤ L.sc.x ^ L.Ct
  Dp_poly : (Dp : ℝ) ≤ L.sc.x ^ L.Ct
  TO_poly : (TO : ℝ) ≤ L.sc.x ^ L.Ct

  nW_win : nW L P.CnW ≤ (nWn : ℝ) ∧ (nWn : ℝ) < nW L P.CnW + 8
  nW_dvd : 8 ∣ nWn

  PP_nW : (2 * (D.R.f : ℝ) * D.R.m) ^ 4 * (nWn : ℝ) ≤ PP

  nW_le : (nWn : ℝ) ≤ PP

  nW_lo : D.R.f * D.R.r * (D.R.r + 1) ≤ nWn ∧ (D.R.k - 1) * D.R.f + 2 * D.R.r ≤ nWn ∧ nP ≤ nWn

  split : D.R.r + D.R.t = nP + TO * nWn
  nP_eq : nP = 8 * D.R.f * D.R.r + 4

  TO_eq : TO = ⌈L.sc.x ^ cTO⌉₊

  TO_ge : PP ^ 4 * (Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ Cp / ((D.R.m : ℝ) * L.de2) ≤ (TO : ℝ)

  TO_PP : (TO : ℝ) * PP * L.sc.x ^ Cb ≤ L.sc.b

  TO_nW : (Dp + 2) * nWn + 2 * D.R.r ≤ TO

  TO_40 : 40 * (Dp + 2) ≤ TO

  TO_11D2 : 11 * Dp ^ 2 ≤ TO

  order_ge_rank_bound : D.R.r + 2 * (2 * 5 ^ 4 * D.R.r) * (Dp + 1) ≤ TO

  TO_PP' : (TO : ℝ) * PP ≤ L.sc.b ^ (1 / 2 : ℝ)

  precision_cube_order_sq_le : PP ^ 3 * (TO : ℝ) ^ 2 * L.sc.x ^ Cb ≤ L.sc.b

  precision_cube_order_sq_le_sqrt : PP ^ 3 * (TO : ℝ) ^ 2 ≤ L.sc.b ^ (1 / 2 : ℝ)

  TO_Dk : (Dp : ℝ) * D.R.k / D.R.m ≤ (TO : ℝ)

  Del_TO : ((TO : ℝ)) ^ 2 ≤ ((D.s.Del : ℚ) : ℝ)

  Del_gap : ((TO : ℝ) + Dp + 2) * ((TO : ℝ) + Dp + 2 + 2 * (D.R.N D.R.m : ℝ)) ≤ ((D.s.Del : ℚ) : ℝ)

  heightBound_ge_order_sq : 4 * (TO : ℝ) ^ 2 + 2 * D.R.t ≤ h0 L

  heightBound_ge_precision_degree : PP * Dp * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) * TO ≤ h0 L

  heightBound_ge_precision_cubic : PP * ((D.R.f : ℝ) * D.R.m * D.R.k) ^ 3 * D.R.k / D.R.m ≤ h0 L

  heightBound_ge_order_product : ChT * TO * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * Dp * PP ≤ h0 L

  log_bound_le_sqrt : (TO : ℝ) * (Dp : ℝ) ^ 2 * Real.log L.sc.b * L.sc.x ^ Cb ≤ L.sc.b

  TD2' : (TO : ℝ) * (Dp : ℝ) ^ 2 * Real.log L.sc.b ≤ L.sc.b ^ (1 / 2 : ℝ)

  b_ge : CbN * (D.R.r : ℝ) * D.R.m * D.R.k * PP ^ 2 * (Dp : ℝ) ^ 3 ≤ L.sc.b

  s_odd : Odd s
  s_lo : D.R.r + 5 < s
  s_hi : s ≤ D.R.r + 7

theorem ParamsT.Cp_nonneg {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : 0 ≤ T.Cp :=
  le_trans zero_le_one T.Cp_ge

theorem ParamsT.order_ge_max_linear_square {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    4 * T.Dp + 4 ≤ T.TO ∧ T.Dp ^ 2 ≤ T.TO :=
  ⟨le_trans (by omega) T.TO_40, le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) T.TO_11D2⟩

theorem ParamsT.nW_40 {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : 40 ≤ T.nWn := by
  have hf : 2 ≤ D.R.f := by
    have := D.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hr : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have h3 : 2 * 6 * (6 + 1) ≤ D.R.f * D.R.r * (D.R.r + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul hf hr) (by omega)
  exact le_trans (by norm_num) (le_trans h3 T.nW_lo.1)

theorem ParamsT.nW_even {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : Even T.nWn :=
  (even_iff_two_dvd.2 (Dvd.dvd.trans (by norm_num) T.nW_dvd))

theorem ParamsT.nP_ge {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    8 * D.R.f * D.R.r + 4 ≤ T.nP := T.nP_eq.ge

theorem ParamsT.four_dvd_nP {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : 4 ∣ T.nP := by
  rw [T.nP_eq]; exact ⟨2 * D.R.f * D.R.r + 1, by ring⟩

theorem ParamsT.even_nP₂ {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : Even T.nP :=
  even_iff_two_dvd.2 (Dvd.dvd.trans (by norm_num) T.four_dvd_nP)

theorem ParamsT.PP_pos {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P)
    (hZ : 0 < zBase L) : 0 < T.PP := by
  rw [T.PP_eq]; have := T.one_le_CP; positivity

end Formalism.BasicNotions

end
