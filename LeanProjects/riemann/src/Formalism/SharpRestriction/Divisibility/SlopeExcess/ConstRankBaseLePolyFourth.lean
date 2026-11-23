import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.KernelPlaceMeanBound
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FourMulQLeCondN

noncomputable section

namespace Formalism.MainNotions.DIV.Proofs.HHParts

open Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} (L : SizeData₂ D)

def _root_.Formalism.MainNotions.DIV.Proofs.szPol : ℝ := 1 + (D.R.f : ℝ) + D.R.k + D.R.m + D.R.t + (D.R.N D.R.m : ℝ) + L.sc.L

theorem sc_x_pos : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt

theorem sc_L_pos : 0 < L.sc.L := Real.rpow_pos_of_pos (sc_x_pos L) _

theorem one_le_szPol : 1 ≤ szPol L := by
  unfold szPol
  have h1 : (0:ℝ) ≤ L.sc.L := (sc_L_pos L).le
  have : (0:ℝ) ≤ (D.R.f:ℝ) + D.R.k + D.R.m + D.R.t + (D.R.N D.R.m : ℝ) := by positivity
  linarith

theorem f_le : (D.R.f : ℝ) ≤ szPol L := by
  unfold szPol; have := (sc_L_pos L).le; have : (0:ℝ) ≤ D.R.k + D.R.m + D.R.t + (D.R.N D.R.m : ℝ) := by positivity
  linarith
theorem k_le : (D.R.k : ℝ) ≤ szPol L := by
  unfold szPol; have := (sc_L_pos L).le; have : (0:ℝ) ≤ D.R.f + D.R.m + D.R.t + (D.R.N D.R.m : ℝ) := by positivity
  linarith
theorem m_le : (D.R.m : ℝ) ≤ szPol L := by
  unfold szPol; have := (sc_L_pos L).le; have : (0:ℝ) ≤ D.R.f + D.R.k + D.R.t + (D.R.N D.R.m : ℝ) := by positivity
  linarith
theorem t_le : (D.R.t : ℝ) ≤ szPol L := by
  unfold szPol; have := (sc_L_pos L).le; have : (0:ℝ) ≤ D.R.f + D.R.k + D.R.m + (D.R.N D.R.m : ℝ) := by positivity
  linarith
theorem N_le : (D.R.N D.R.m : ℝ) ≤ szPol L := by
  unfold szPol; have := (sc_L_pos L).le; have : (0:ℝ) ≤ D.R.f + D.R.k + D.R.m + (D.R.t : ℝ) := by positivity
  linarith
theorem L_le : L.sc.L ≤ szPol L := by
  unfold szPol; have : (0:ℝ) ≤ D.R.f + D.R.k + D.R.m + (D.R.t : ℝ) + (D.R.N D.R.m : ℝ) := by positivity
  linarith

theorem Nj_le (j : ℕ) (hj : j ≤ D.R.m) : (D.R.N j : ℝ) ≤ szPol L := by
  refine le_trans ?_ (N_le L)
  unfold Ranks.N; push_cast
  have : (j : ℝ) ≤ D.R.m := by exact_mod_cast hj
  have : (0:ℝ) ≤ D.R.t + 1 := by positivity
  nlinarith

theorem nV_le : (D.R.nV : ℝ) ≤ szPol L := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Formalism.BasicNotions.DV.nV_cast D.R)
  push_cast at h
  rw [h]
  unfold szPol; have := (sc_L_pos L).le; have : (0:ℝ) ≤ D.R.f + (D.R.N D.R.m : ℝ) := by positivity
  linarith

theorem one_le_b : 1 ≤ L.sc.b := by
  unfold Scale.b; exact Real.one_le_exp (sc_L_pos L).le

theorem x_le_k (h : SizeK L) : L.sc.x ≤ D.R.k := by
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) := by
    conv_lhs => rw [← Real.rpow_one L.sc.x]
    apply Real.rpow_le_rpow_of_exponent_le hx.le
    unfold szTh; linarith [L.sc.eps_lt]
  exact this.trans h.1

theorem x_le (h : SizeK L) : L.sc.x ≤ szPol L := (x_le_k L h).trans (k_le L)

theorem a_nonneg : 0 ≤ L.sc.a := by
  unfold Scale.a; exact mul_nonneg (sc_x_pos L).le (by linarith [one_le_b L])

theorem a_le (h : SizeK L) : L.sc.a ≤ szPol L * L.sc.b := by
  unfold Scale.a; exact mul_le_mul_of_nonneg_right (x_le L h) (by linarith [one_le_b L])

theorem one_le_X' : 1 ≤ L.sc.X' := by
  unfold Scale.X'; exact Real.one_le_exp (Real.rpow_pos_of_pos (sc_x_pos L) _).le

theorem b'_nonneg : 0 ≤ L.sc.b' := by
  unfold Scale.b'; exact div_nonneg (a_nonneg L) (by linarith [one_le_X' L])

theorem b'_le_a : L.sc.b' ≤ L.sc.a := by
  unfold Scale.b'; exact div_le_self (a_nonneg L) (one_le_X' L)

variable {L}

theorem n_pos (hN : SizeN L) : 1 ≤ (D.R.n : ℝ) := by
  have h := lt_of_lt_of_le (Real.rpow_pos_of_pos (sc_x_pos L) _) hN.1
  have : 0 < D.R.n := by exact_mod_cast h
  exact_mod_cast this

theorem f_eq : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring

theorem k_one (hK : SizeK L) : 1 ≤ (D.R.k : ℝ) := by linarith [x_le_k L hK, L.sc.one_lt_alt]

theorem w''_nonneg : 0 ≤ L.sc.w'' D.R.n := by
  unfold Scale.w''; exact div_nonneg (b'_nonneg L) (mul_nonneg (sc_x_pos L).le (Nat.cast_nonneg _))

theorem w''_le (hN : SizeN L) : L.sc.w'' D.R.n ≤ L.sc.b' := by
  unfold Scale.w''
  apply div_le_self (b'_nonneg L)
  have := n_pos hN; have := L.sc.one_lt_alt; nlinarith

theorem Sc_le (hK : SizeK L) (hDel : SizeDel L) : L.Sc ≤ L.sc.w'' D.R.n := by
  have h4 := hDel.2.2.2.1
  have := k_one hK; have := L.Sc_pos
  nlinarith

theorem Sc_le' (hN : SizeN L) (hK : SizeK L) (hDel : SizeDel L) : L.Sc ≤ szPol L * L.sc.b :=
  (Sc_le hK hDel).trans ((w''_le hN).trans ((b'_le_a L).trans (a_le L hK)))

theorem eta_le (hN : SizeN L) (hK : SizeK L) (hEta : SizeEta L) : L.etaSz ≤ L.sc.b := by
  refine hEta.2.1.trans (div_le_self (by linarith [one_le_b L]) ?_)
  have ht : (1:ℝ) ≤ D.R.t := L.t_win.1
  have hf : (1:ℝ) ≤ D.R.f := by rw [f_eq]; linarith [n_pos hN]
  have hk := k_one hK
  have h1 : (1:ℝ) ≤ (D.R.t : ℝ) ^ 3 := one_le_pow₀ ht
  have h2 : (1:ℝ) ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hk
  calc (1:ℝ) = 1 * 1 * 1 := by ring
    _ ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := by gcongr

theorem delta1_le : L.sc.delta1 ≤ 1 := by
  unfold Scale.delta1
  exact Real.rpow_le_one_of_one_le_of_nonpos L.sc.one_lt_alt.le (by linarith [L.sc.eps_pos])

theorem TT_le (hTT : SizeTT L) : (D.host.TT.card : ℝ) ≤ szPol L := by
  refine hTT.2.trans (le_trans ?_ (f_le L))
  unfold szNst; rw [f_eq]
  have := delta1_le (L := L)
  have h0 : (0:ℝ) ≤ D.R.n := Nat.cast_nonneg _
  nlinarith

theorem xth_le : L.sc.x ^ szTh L ≤ L.sc.L := by
  unfold Scale.L szTh
  apply Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le
  linarith [L.sc.eps_pos]

theorem LaG_le (hLa : SizeLa L) : L.LaG ≤ L.sc.L ^ 2 := by
  refine hLa.2.trans ?_
  rw [Real.rpow_add (sc_x_pos L), sq]
  exact mul_le_mul_of_nonneg_left xth_le (Real.rpow_pos_of_pos (sc_x_pos L) _).le

theorem LaG_pos (hLa : SizeLa L) : 0 < L.LaG := lt_of_lt_of_le (Real.rpow_pos_of_pos (sc_x_pos L) _) hLa.1

theorem bT_nonneg (t : D.host.TT) : 0 ≤ (L.bT t : ℝ) := (b'_nonneg L).trans (L.bT_ge t)

theorem bT_le (hK : SizeK L) (hLa : SizeLa L) (hBot : SizeBot L) (t : D.host.TT) :
    (L.bT t : ℝ) ≤ 2 * szPol L ^ 5 * L.sc.b := by
  have hP := one_le_szPol L
  have hb := one_le_b L
  have hk := k_one hK
  have hNs : szNst L ≤ szPol L := by
    unfold szNst; refine le_trans ?_ (f_le L); rw [f_eq]
    have := delta1_le (L := L); have h0 : (0:ℝ) ≤ D.R.n := Nat.cast_nonneg _
    nlinarith
  have hNs0 : 0 ≤ szNst L := by
    unfold szNst; have : 0 ≤ L.sc.delta1 := (Real.rpow_pos_of_pos (sc_x_pos L) _).le
    positivity
  have hxe : L.sc.x ^ L.sc.eps ≤ szPol L := L_le L
  have hxe0 : 0 ≤ L.sc.x ^ L.sc.eps := (sc_L_pos L).le
  have hG : L.LaG ≤ szPol L ^ 2 := (LaG_le hLa).trans (pow_le_pow_left₀ (sc_L_pos L).le (L_le L) 2)
  have hG0 := (LaG_pos hLa).le
  have hb' : L.sc.b' ≤ szPol L * L.sc.b := (b'_le_a L).trans (a_le L hK)
  have hb'0 := b'_nonneg L
  have e1 : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' ≤ szPol L * szPol L * szPol L ^ 2 * (szPol L * L.sc.b) := by
    apply mul_le_mul _ hb' hb'0 (by positivity)
    apply mul_le_mul _ hG hG0 (by positivity)
    exact mul_le_mul hNs hxe hxe0 (by positivity)
  have e2 : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k ≤ szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' :=
    div_le_self (by positivity) hk
  have := hBot t
  have h5 : szPol L * L.sc.b ≤ szPol L ^ 5 * L.sc.b := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    calc szPol L = szPol L ^ 1 := (pow_one _).symm
      _ ≤ szPol L ^ 5 := pow_le_pow_right₀ hP (by norm_num)
  have h6 : szPol L * szPol L * szPol L ^ 2 * (szPol L * L.sc.b) = szPol L ^ 5 * L.sc.b := by ring
  linarith

theorem aT_bounds (hK : SizeK L) (t : D.host.TT) : 0 ≤ (L.aT t : ℝ) ∧ (L.aT t : ℝ) ≤ 2 * (szPol L * L.sc.b) := by
  obtain ⟨h1, h2⟩ := L.aT_win t
  have ha := a_nonneg L
  have hk := k_one hK
  have hx : (1:ℝ) ≤ L.sc.x ^ (Scale.A / 2) :=
    Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)
  have hd : 1 ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) := by nlinarith
  have : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a := div_le_self ha hd
  constructor
  · linarith
  · linarith [a_le L hK]

theorem q_pos (hQD : SizeQD L) : 1 < (D.host.q : ℝ) := by
  have h := lt_of_lt_of_le (Real.rpow_pos_of_pos (sc_x_pos L) _) hQD.1
  by_contra hc; replace hc := not_lt.1 hc
  have : Real.log (D.host.q : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) hc
  linarith

theorem d_pos (hQD : SizeQD L) : 1 < (D.host.d : ℝ) := by
  have h := lt_of_lt_of_le (Real.rpow_pos_of_pos (sc_x_pos L) _) hQD.2.2.2.1
  by_contra hc; replace hc := not_lt.1 hc
  have : Real.log (D.host.d : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) hc
  linarith

theorem log_rdE_bounds (hN : SizeN L) (hQD : SizeQD L) :
    0 ≤ Real.log D.host.rdE ∧ Real.log D.host.rdE ≤ 2 * szPol L := by
  have hq := q_pos hQD; have hd := d_pos hQD
  obtain ⟨-, -, hq2, -, hd2, -, hr1, -⟩ := hQD
  have hn := n_pos hN
  refine ⟨Real.log_nonneg hr1, ?_⟩
  have e1 := UpperTheory.Ram.Rd.log_rdE_le D.host
  have e2 : Real.log (D.R.n : ℝ) ≤ D.R.n := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < D.R.n by positivity); linarith
  have ex : L.sc.x ^ (L.sc.eps / 5 + szTh L) ≤ L.sc.L := by
    unfold Scale.L szTh
    apply Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le
    linarith [L.sc.eps_pos]
  have := f_le L; have := L_le L; rw [f_eq] at *
  linarith

theorem La_bounds (hN : SizeN L) (hK : SizeK L) (hQD : SizeQD L) : 0 ≤ L.La ∧ L.La ≤ 4 * szPol L := by
  obtain ⟨h0, h1⟩ := log_rdE_bounds hN hQD
  have hr : 1 ≤ D.host.rdE := hQD.2.2.2.2.2.2.1
  have hb := one_le_b L
  have hx := L.sc.one_lt_alt
  unfold SizeData₂.La Scale.a
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have lb : Real.log L.sc.b = L.sc.L := by unfold Scale.b; exact Real.log_exp _
  rw [lb]
  have lx0 : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx.le
  have lx1 : Real.log L.sc.x ≤ L.sc.x := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have := x_le L hK; have := L_le L; have := (sc_L_pos L).le
  constructor <;> linarith

theorem pow_mono_P {a b : ℕ} (h : a ≤ b) : szPol L ^ a ≤ szPol L ^ b := pow_le_pow_right₀ (one_le_szPol L) h

theorem P_le_pow {b : ℕ} (h : 1 ≤ b) : szPol L ≤ szPol L ^ b := by
  calc szPol L = szPol L ^ 1 := (pow_one _).symm
    _ ≤ szPol L ^ b := pow_mono_P h

theorem nV_one (hK : SizeK L) : 1 ≤ (D.R.nV : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Formalism.BasicNotions.DV.nV_cast D.R)
  push_cast at h
  rw [h]
  have := k_one hK
  have : (2:ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have : (0:ℝ) ≤ D.R.t := Nat.cast_nonneg _
  linarith

theorem Lprime_bounds (hN : SizeN L) (hK : SizeK L) (hQD : SizeQD L) (hG : SizeG L) :
    0 ≤ Formalism.BasicNotions.DV.Lprime D L ∧ Formalism.BasicNotions.DV.Lprime D L ≤ 6 * szPol L ^ 2 := by
  obtain ⟨r0, r1⟩ := log_rdE_bounds hN hQD
  have hr : 1 ≤ D.host.rdE := hQD.2.2.2.2.2.2.1
  have hb := one_le_b L
  have hk := k_one hK
  have hv := nV_one hK
  have hkb : 1 ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
  have hg : ∀ i : Fin 2, 1 ≤ (D.host.g i : ℝ) ∧ Real.log (D.host.g i : ℝ) ≤ szPol L ^ 2 := by
    intro i
    obtain ⟨g1, -, g3⟩ := hG i i
    have : 1 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := one_le_pow₀ hkb
    refine ⟨by linarith, g3.trans ?_⟩
    have := xth_le (L := L)
    have h0 := (sc_L_pos L).le
    have hL := L_le L
    calc L.sc.x ^ szTh L * L.sc.L ≤ L.sc.L * L.sc.L := mul_le_mul_of_nonneg_right this h0
      _ ≤ szPol L * szPol L := mul_le_mul hL hL h0 (by linarith [one_le_szPol L])
      _ = szPol L ^ 2 := (sq _).symm
  obtain ⟨g0a, g0b⟩ := hg 0
  obtain ⟨g1a, g1b⟩ := hg 1
  unfold Formalism.BasicNotions.DV.Lprime
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have lb : Real.log L.sc.b = L.sc.L := by unfold Scale.b; exact Real.log_exp _
  rw [lb]
  have l0 := Real.log_nonneg g0a; have l1 := Real.log_nonneg g1a; have lv := Real.log_nonneg hv
  have lv2 : Real.log (D.R.nV : ℝ) ≤ szPol L := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith [nV_le L])
  have := (sc_L_pos L).le; have := L_le L
  have hP := one_le_szPol L
  have hP2 : szPol L ≤ szPol L ^ 2 := P_le_pow (by norm_num)
  constructor <;> nlinarith

theorem logOm_abs (hQD : SizeQD L) (hDel : SizeDel L) :
    |L.logOm| ≤ 7 * szPol L := by
  have hr : 1 ≤ D.host.rdE := hQD.2.2.2.2.2.2.1
  have hv : D.host.v = D.host.rdE / 2 := rfl
  have hvpos : 0 < D.host.v := by rw [hv]; linarith
  have hlv1 : -1 ≤ Real.log D.host.v := by
    have : Real.log (1/2) ≤ Real.log D.host.v := Real.log_le_log (by norm_num) (by rw [hv]; linarith)
    have h2 : Real.log (1/2 : ℝ) = - Real.log 2 := by rw [one_div, Real.log_inv]
    have h3 : Real.log (2:ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    linarith
  have hlv2 : Real.log D.host.v ≤ szPol L := by
    have h8 := hDel.2.2.2.2.2.2.2
    have hxm : 1 ≤ L.sc.x ^ szTh L * D.R.m := by
      have : 1 ≤ L.sc.x ^ szTh L := Real.one_le_rpow L.sc.one_lt_alt.le (by unfold szTh; linarith [L.sc.eps_pos])
      have : (2:ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
      nlinarith
    rcases le_or_gt (Real.log D.host.v) 0 with h | h
    · linarith [one_le_szPol L]
    · have : Real.log D.host.v ≤ L.sc.x ^ szTh L * D.R.m * Real.log D.host.v := by nlinarith
      linarith [k_le L]
  have hpi : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos; linarith [Real.pi_le_four]
  have hpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hdl := hQD.2.2.2.2.2.1
  have hL := L_le L
  have hg1 := Real.eulerMascheroniConstant_lt_two_thirds
  have hg0 := Real.one_half_lt_eulerMascheroniConstant
  have e : L.logOm = Real.eulerMascheroniConstant + (Real.log Real.pi - Real.log D.host.v) - L.logDerivativeAtOne := by
    show Real.eulerMascheroniConstant + Real.log (Real.pi / D.host.v) - L.logDerivativeAtOne = _
    rw [Real.log_div Real.pi_pos.ne' hvpos.ne']
  rw [e, abs_le]
  have := abs_le.1 hdl
  have hx : L.sc.x ^ L.sc.eps = L.sc.L := rfl
  have hP := one_le_szPol L
  constructor <;> linarith [this.1, this.2]

theorem wj_eq (τ : D.what₂.Tau) (q : Fin D.R.m) : wj D (q.1 + 1) τ = (((D.hc τ).e q : ℚ) : ℝ) := by
  unfold wj; simp

theorem top_or (τ : D.what₂.Tau) :
    (∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t) ∨
      (D.eTau τ : D.R.GG) ∉ D.host.topPlaces := by
  by_cases h : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · left
    obtain ⟨a, ha, he⟩ := Finset.mem_image.1 h
    exact ⟨⟨a, ha⟩, he.symm⟩
  · exact Or.inr h

theorem Pb_le (k : ℕ) (hk : 1 ≤ k) : szPol L * L.sc.b ≤ szPol L ^ k * L.sc.b :=
  mul_le_mul_of_nonneg_right (P_le_pow hk) (by linarith [one_le_b L])

theorem b_le_poly_fifth_mul_b : L.sc.b ≤ szPol L ^ 5 * L.sc.b := by
  have : (1:ℝ) ≤ szPol L ^ 5 := one_le_pow₀ (one_le_szPol L)
  have := one_le_b L; nlinarith

theorem e_bounds (hN : SizeN L) (hK : SizeK L) (hLa : SizeLa L) (hBot : SizeBot L) (hEta : SizeEta L)
    (τ : D.what₂.Tau) (q : Fin D.R.m) :
    0 ≤ (((D.hc τ).e q : ℚ) : ℝ) ∧ (((D.hc τ).e q : ℚ) : ℝ) ≤ 4 * szPol L ^ 5 * L.sc.b := by
  rw [← wj_eq]
  have hb := one_le_b L
  have he := eta_le hN hK hEta
  have he0 := L.etaSz_pos.le
  have h5 := b_le_poly_fifth_mul_b (L := L)
  have hPb := Pb_le (L := L) 5 (by norm_num)
  rcases top_or τ with ⟨t, ht⟩ | hnt
  · obtain ⟨w1, w2⟩ := L.win_top (q.1 + 1) (by omega) (by omega) τ t ht
    have hbt := bT_le hK hLa hBot t
    have hbt0 := bT_nonneg (L := L) t
    have hx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self (b'_nonneg L) L.sc.one_lt_alt.le
    have hx0 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (b'_nonneg L) (sc_x_pos L).le
    have hb' : L.sc.b' ≤ szPol L * L.sc.b := (b'_le_a L).trans (a_le L hK)
    constructor <;> linarith
  · by_cases hth : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · obtain ⟨w1, w2⟩ := L.win_thick (q.1 + 1) (by omega) (by omega) τ hth
      constructor <;> linarith
    · have hthin : D.host.IsThin (D.eTau τ : D.R.GG) := ⟨(D.eTau τ).2, hnt, hth⟩
      obtain ⟨w1, w2⟩ := L.win_thin (q.1 + 1) (by omega) (by omega) τ hthin
      have h1 := w''_nonneg (L := L)
      have h2 : L.sc.w'' D.R.n ≤ szPol L * L.sc.b := (w''_le hN).trans ((b'_le_a L).trans (a_le L hK))
      constructor <;> linarith

theorem b_abs (hN : SizeN L) (hK : SizeK L) (hLa : SizeLa L) (hBot : SizeBot L) (hEta : SizeEta L)
    (τ : D.what₂.Tau) (q : Fin D.R.m) : |(((D.hc τ).b q : ℚ) : ℝ)| ≤ 5 * szPol L ^ 5 * L.sc.b := by
  obtain ⟨e0, e1⟩ := e_bounds hN hK hLa hBot hEta τ q
  have g := (D.hc τ).gap_be q
  have g' : (((D.R.t : ℚ) + 3) / 2 : ℚ) ≤ ((D.hc τ).e q - (D.hc τ).b q : ℚ) := g
  have gr : ((D.R.t : ℝ) + 3) / 2 ≤ (((D.hc τ).e q : ℚ) : ℝ) - (((D.hc τ).b q : ℚ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 g'; push_cast at this; linarith
  have c := L.be_close τ q q
  push_cast at c
  have c' := abs_le.1 c
  have he := eta_le hN hK hEta
  have h5 := b_le_poly_fifth_mul_b (L := L)
  have ht : (0:ℝ) ≤ D.R.t := Nat.cast_nonneg _
  rw [abs_le]; constructor <;> linarith [c'.1, c'.2]

theorem k_two (hK : SizeK L) : 2 ≤ D.R.k := by
  have h := x_le_k L hK
  have h1 := L.sc.one_lt_alt
  have : (1:ℝ) < D.R.k := by linarith
  have : 1 < D.R.k := by exact_mod_cast this
  omega

theorem u_abs (P5 : ParameterChoice' D L) (hN : SizeN L) (hK : SizeK L) (hLa : SizeLa L) (hBot : SizeBot L)
    (hDel : SizeDel L) (w : D.what₂.Word) (τ : D.what₂.Tau) (i : Fin D.R.k) :
    |(((D.hcW w τ).u i : ℚ) : ℝ)| ≤ 3 * szPol L ^ 5 * L.sc.b := by
  have hk2 := k_two hK
  have hSc := Sc_le' hN hK hDel
  have hSc0 := L.Sc_pos.le
  have hb := one_le_b L
  have hP := one_le_szPol L
  have hPb := Pb_le (L := L) 5 (by norm_num)
  have hkP := k_le L
  have hP5 : szPol L ≤ szPol L ^ 5 * L.sc.b := by
    have := P_le_pow (L := L) (b := 5) (by norm_num)
    have : 0 ≤ szPol L ^ 5 := by positivity
    nlinarith
  obtain ⟨iv, hiv⟩ := i
  by_cases h0 : iv = 0
  · subst h0
    have hk0 : 0 < D.R.k := by omega
    rw [D.hcW_first w τ hk0]
    rcases top_or τ with ⟨t, ht⟩ | hnt
    · rw [(L.top_u τ t hk0 ht).1]
      obtain ⟨a0, a1⟩ := aT_bounds hK t
      rw [abs_le]; constructor <;> nlinarith
    · have hk1 : 0 < D.R.k - 1 := by omega
      have c1 := P5.cloud_place_bound τ hk1 hnt
      have c2 := (D.hc τ).u_gt_v ⟨0, hk1⟩
      have c2' : (((D.hc τ).v ⟨0, hk1⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨0, hk0⟩ : ℚ) : ℝ) := by exact_mod_cast c2
      push_cast at c1
      obtain ⟨v0, v1⟩ := L.cloud_v τ ⟨0, hk1⟩
      rw [abs_le]; constructor <;> nlinarith
  · by_cases hl : iv = D.R.k - 1
    · subst hl
      have hk0 : 0 < D.R.k := by omega
      rw [D.hcW_last w τ hk0]
      rcases top_or τ with ⟨t, ht⟩ | hnt
      · rw [(L.top_u τ t hk0 ht).2]
        have hbt := bT_le hK hLa hBot t
        have hbt0 := bT_nonneg (L := L) t
        rw [abs_le]; constructor <;> nlinarith
      · have c := P5.uk_extreme τ hk2 hnt
        have c' : (((D.hc τ).u ⟨D.R.k - 1, by omega⟩ : ℚ) : ℝ) = (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ : ℚ) : ℝ) - 1 / 2 := by
          rw [c]; push_cast; ring
        rw [c']
        obtain ⟨v0, v1⟩ := L.cloud_v τ ⟨D.R.k - 2, by omega⟩
        rw [abs_le]; constructor <;> nlinarith
    · obtain ⟨c0, c1⟩ := L.cloud_u w τ ⟨iv, hiv⟩ (by simp; omega) (by simp; omega)
      rw [abs_le]; constructor <;> nlinarith

theorem phF_lower (y M : ℝ) (hM : 1 ≤ M) (hy : |y| ≤ M) : -(M * Real.log M + M + 1) ≤ phF y := by
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have key : |y * Real.log y| ≤ M * Real.log M + 1 := by
    rw [← Real.log_abs y, abs_mul]
    rcases le_or_gt |y| 1 with h | h
    · rcases eq_or_lt_of_le (abs_nonneg y) with h0 | h0
      · rw [← h0]; simp; nlinarith
      · have := Real.abs_log_mul_self_lt |y| h0 h
        rw [abs_mul, abs_abs, mul_comm] at this
        nlinarith
    · have hl0 : 0 ≤ Real.log |y| := Real.log_nonneg h.le
      have hl1 : Real.log |y| ≤ Real.log M := Real.log_le_log (by linarith) hy
      rw [abs_of_nonneg hl0]
      have : |y| * Real.log |y| ≤ M * Real.log M := mul_le_mul hy hl1 hl0 (by linarith)
      linarith
  unfold phF
  have := abs_le.1 key
  have := abs_le.1 hy
  linarith [this.1]

theorem srcPar_abs (P5 : ParameterChoice' D L) (hN : SizeN L) (hK : SizeK L) (hLa : SizeLa L) (hBot : SizeBot L)
    (hEta : SizeEta L) (hDel : SizeDel L) (w : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) :
    |((Formalism.BasicNotions.DV.srcPar D w τ i : ℚ) : ℝ)| ≤ 5 * szPol L ^ 5 * L.sc.b := by
  have hb := one_le_b L
  have hP := one_le_szPol L
  have hP5 : szPol L ≤ szPol L ^ 5 * L.sc.b := by
    have := P_le_pow (L := L) (b := 5) (by norm_num)
    have : 0 ≤ szPol L ^ 5 := by positivity
    nlinarith
  have hPb0 : 0 ≤ szPol L ^ 5 * L.sc.b := by positivity
  unfold Formalism.BasicNotions.DV.srcPar
  split_ifs with h1 h2
  · have := u_abs P5 hN hK hLa hBot hDel w τ ⟨i, h1⟩
    linarith
  · rw [D.hcW_e w τ]
    obtain ⟨e0, e1⟩ := e_bounds hN hK hLa hBot hEta τ ⟨(i - D.R.k) / (D.R.t + 1), h2⟩
    set c : ℕ := (i - D.R.k) % (D.R.t + 1) + 1 with hc
    have hc1 : 1 ≤ c := by omega
    have hc2 : c ≤ D.R.t + 1 := by have := Nat.mod_lt (i - D.R.k) (show 0 < D.R.t + 1 by omega); omega
    have hc1' : (1:ℝ) ≤ c := by exact_mod_cast hc1
    have hc2' : (c:ℝ) ≤ D.R.t + 1 := by exact_mod_cast hc2
    have ht := t_le L
    push_cast
    rw [abs_le]; constructor <;> nlinarith
  · simp; positivity

theorem wSz_abs (hN : SizeN L) (hK : SizeK L) (hLa : SizeLa L) (hBot : SizeBot L) (hEta : SizeEta L)
    (j : ℕ) (τ : D.what₂.Tau) : |Formalism.BasicNotions.DV.wSz D j τ| ≤ 4 * szPol L ^ 5 * L.sc.b := by
  unfold Formalism.BasicNotions.DV.wSz
  split_ifs with h
  · obtain ⟨e0, e1⟩ := e_bounds hN hK hLa hBot hEta τ ⟨j - 1, by omega⟩
    rw [abs_of_nonneg e0]; exact e1
  · simp; have := one_le_b L; have := one_le_szPol L; positivity

theorem nuRow_abs (P5 : ParameterChoice' D L) (hN : SizeN L) (hK : SizeK L) (hLa : SizeLa L) (hBot : SizeBot L)
    (hEta : SizeEta L) (hDel : SizeDel L) (w : D.what₂.Word) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (i : ℕ)
    (hi : i < D.R.N (j - 1)) : |Formalism.BasicNotions.DV.nuRow D w j τ i| ≤ 11 * szPol L ^ 5 * L.sc.b := by
  have h1 := srcPar_abs P5 hN hK hLa hBot hEta hDel w τ i
  have h2 := wSz_abs hN hK hLa hBot hEta j τ
  have hN1 := Nj_le L (j - 1) (by omega)
  have hN2 := Nj_le L j hj
  have hi' : (i : ℝ) < D.R.N (j - 1) := by exact_mod_cast hi
  have hb := one_le_b L
  have hP := one_le_szPol L
  have hP5 : szPol L ≤ szPol L ^ 5 * L.sc.b := by
    have := P_le_pow (L := L) (b := 5) (by norm_num)
    have : 0 ≤ szPol L ^ 5 := by positivity
    nlinarith
  have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
  unfold Formalism.BasicNotions.DV.nuRow
  rw [abs_le] at *
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem log_M_le :
    Real.log (11 * szPol L ^ 5 * L.sc.b) ≤ 16 * szPol L := by
  have hb := one_le_b L
  have hP := one_le_szPol L
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have lb : Real.log L.sc.b = L.sc.L := by unfold Scale.b; exact Real.log_exp _
  rw [lb]
  have l11 : Real.log (11:ℝ) ≤ 10 := by have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 11 by norm_num); linarith
  have lP : Real.log (szPol L) ≤ szPol L := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have := L_le L
  push_cast
  nlinarith

theorem kerPlace_lower (P5 : ParameterChoice' D L) (hN : SizeN L) (hK : SizeK L) (hQD : SizeQD L) (hLa : SizeLa L)
    (hBot : SizeBot L) (hEta : SizeEta L) (hDel : SizeDel L) (w : D.what₂.Word) (j : ℕ) (hj : j ≤ D.R.m)
    (τ : D.what₂.Tau) : -(300 * szPol L ^ 7 * L.sc.b) ≤ Formalism.BasicNotions.DV.kerPlace D L w j τ := by
  set M : ℝ := 11 * szPol L ^ 5 * L.sc.b with hMdef
  have hb := one_le_b L
  have hP := one_le_szPol L
  have hM1 : 1 ≤ M := by
    have : (1:ℝ) ≤ szPol L ^ 5 := one_le_pow₀ hP
    rw [hMdef]; nlinarith
  have hnu : ∀ i ∈ Finset.range (D.R.N (j - 1)), |Formalism.BasicNotions.DV.nuRow D w j τ i| ≤ M := fun i hi =>
    nuRow_abs P5 hN hK hLa hBot hEta hDel w j hj τ i (Finset.mem_range.1 hi)
  have hOm := logOm_abs hQD hDel (L := L)
  set n := D.R.N (j - 1)
  have s1 : ∑ i ∈ Finset.range n, -(M * Real.log M + M + 1) ≤
      ∑ i ∈ Finset.range n, phF (Formalism.BasicNotions.DV.nuRow D w j τ i) :=
    Finset.sum_le_sum fun i hi => phF_lower _ M hM1 (hnu i hi)
  have s2 : |∑ i ∈ Finset.range n, Formalism.BasicNotions.DV.nuRow D w j τ i| ≤ ∑ i ∈ Finset.range n, M :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hnu)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at s1 s2
  have s3 : (∑ i ∈ Finset.range n, Formalism.BasicNotions.DV.nuRow D w j τ i) * L.logOm ≤ n * M * (7 * szPol L) := by
    calc _ ≤ |(∑ i ∈ Finset.range n, Formalism.BasicNotions.DV.nuRow D w j τ i) * L.logOm| := le_abs_self _
      _ = |∑ i ∈ Finset.range n, Formalism.BasicNotions.DV.nuRow D w j τ i| * |L.logOm| := abs_mul _ _
      _ ≤ n * M * (7 * szPol L) := mul_le_mul s2 hOm (abs_nonneg _) (by positivity)
  have hlM := log_M_le (L := L)
  have hlM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hn : (n : ℝ) ≤ szPol L := Nj_le L (j - 1) (by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hK1 : M * Real.log M + M + 1 + M * (7 * szPol L) ≤ 300 * szPol L ^ 6 * L.sc.b := by
    have e1 : M * Real.log M ≤ M * (16 * szPol L) := mul_le_mul_of_nonneg_left hlM (by linarith)
    have e2 : M ≤ M * szPol L := le_mul_of_one_le_right (by linarith) hP
    have e3 : (1:ℝ) ≤ szPol L ^ 6 * L.sc.b := by have : (1:ℝ) ≤ szPol L ^ 6 := one_le_pow₀ hP; nlinarith
    have e4 : M * szPol L = 11 * szPol L ^ 6 * L.sc.b := by rw [hMdef]; ring
    nlinarith
  have hK2 : (n : ℝ) * (M * Real.log M + M + 1 + M * (7 * szPol L)) ≤ szPol L * (300 * szPol L ^ 6 * L.sc.b) :=
    mul_le_mul hn hK1 (by positivity) (by linarith)
  have e5 : szPol L * (300 * szPol L ^ 6 * L.sc.b) = 300 * szPol L ^ 7 * L.sc.b := by ring
  unfold Formalism.BasicNotions.DV.kerPlace
  nlinarith

theorem logGamma_le (y : ℝ) (hy : 2 ≤ y) : Real.log (Real.Gamma y) ≤ y * Real.log y := by
  have hn1 : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have hn2 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one (by linarith)
  have h2n : (2:ℝ) ≤ (⌈y⌉₊ : ℝ) := le_trans hy hn1
  have h2n' : 2 ≤ ⌈y⌉₊ := by exact_mod_cast h2n
  set n := ⌈y⌉₊ with hn
  have hm : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by rw [Nat.cast_sub (by omega)]; ring
  have hΓ : Real.Gamma y ≤ Real.Gamma n :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.2 hy) (Set.mem_Ici.2 h2n) hn1
  rw [hm, Real.Gamma_nat_eq_factorial] at hΓ
  have hf : ((n - 1).factorial : ℝ) ≤ ((n - 1 : ℕ) : ℝ) ^ (n - 1) := by exact_mod_cast Nat.factorial_le_pow (n - 1)
  have hpos : 0 < Real.Gamma y := Real.Gamma_pos_of_pos (by linarith)
  have e1 := Real.log_le_log hpos (hΓ.trans hf)
  rw [Real.log_pow] at e1
  have hc1 : (1:ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega)]; push_cast; linarith
  have hc2 : ((n - 1 : ℕ) : ℝ) ≤ y := by rw [Nat.cast_sub (by omega)]; push_cast; linarith
  have l0 : 0 ≤ Real.log ((n - 1 : ℕ) : ℝ) := Real.log_nonneg hc1
  have l1 : Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log y := Real.log_le_log (by linarith) hc2
  calc Real.log (Real.Gamma y) ≤ ((n - 1 : ℕ) : ℝ) * Real.log ((n - 1 : ℕ) : ℝ) := e1
    _ ≤ y * Real.log y := mul_le_mul hc2 l1 l0 (by linarith)

theorem sigPar_step (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    (((Formalism.BasicNotions.DV.sigPar D τ (i + 1) : ℚ) : ℝ)) + 1 ≤ ((Formalism.BasicNotions.DV.sigPar D τ i : ℚ) : ℝ) := by
  have hm2 := D.R.two_le_m
  by_cases h1 : i + 1 < D.R.k - 1
  · have e1 : Formalism.BasicNotions.DV.sigPar D τ i = (D.hc τ).v ⟨i, by omega⟩ := by
      unfold Formalism.BasicNotions.DV.sigPar; rw [dif_pos (by omega)]
    have e2 : Formalism.BasicNotions.DV.sigPar D τ (i + 1) = (D.hc τ).v ⟨i + 1, h1⟩ := by
      unfold Formalism.BasicNotions.DV.sigPar; rw [dif_pos h1]
    have a1 := (D.hc τ).u_gt_v ⟨i + 1, h1⟩
    have a2 := (D.hc τ).v_gt_u ⟨i, by omega⟩
    have lt : (D.hc τ).v ⟨i + 1, h1⟩ < (D.hc τ).v ⟨i, by omega⟩ := lt_trans a1 a2
    obtain ⟨z1, hz1⟩ := (D.hc τ).v_int ⟨i + 1, h1⟩
    obtain ⟨z2, hz2⟩ := (D.hc τ).v_int ⟨i, by omega⟩
    rw [e1, e2, hz1, hz2]
    rw [hz1, hz2] at lt
    have : z1 < z2 := by exact_mod_cast lt
    have : z1 + 1 ≤ z2 := this
    push_cast
    exact_mod_cast this
  · by_cases h2 : i + 1 = D.R.k - 1
    · have hk2 : 2 ≤ D.R.k := by omega
      have e1 : Formalism.BasicNotions.DV.sigPar D τ i = (D.hc τ).v ⟨i, by omega⟩ := by
        unfold Formalism.BasicNotions.DV.sigPar; rw [dif_pos (by omega)]
      have e2 : Formalism.BasicNotions.DV.sigPar D τ (i + 1) = -(D.hc τ).b ⟨0, by omega⟩ := by
        unfold Formalism.BasicNotions.DV.sigPar; rw [dif_neg (by omega), dif_pos (by omega)]
        congr 2; ext; simp; omega
      have a2 := (D.hc τ).v_gt_u ⟨i, by omega⟩
      have a3 := (D.hc τ).u_last_gt (by omega) (by omega)
      have a2' : (D.hc τ).u ⟨D.R.k - 1, by omega⟩ < (D.hc τ).v ⟨i, by omega⟩ := by
        have : (⟨i + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := by ext; simp; omega
        rw [← this]; exact a2
      have lt : -(D.hc τ).b ⟨0, by omega⟩ < (D.hc τ).v ⟨i, by omega⟩ := lt_trans a3 a2'
      obtain ⟨z1, hz1⟩ := (D.hc τ).b_int ⟨0, by omega⟩
      obtain ⟨z2, hz2⟩ := (D.hc τ).v_int ⟨i, by omega⟩
      rw [e1, e2, hz1, hz2]
      rw [hz1, hz2] at lt
      have : -z1 < z2 := by exact_mod_cast lt
      have : -z1 + 1 ≤ z2 := this
      push_cast
      exact_mod_cast this
    · have e1 : Formalism.BasicNotions.DV.sigPar D τ i = -(D.hc τ).b ⟨i - (D.R.k - 1), by omega⟩ := by
        unfold Formalism.BasicNotions.DV.sigPar; rw [dif_neg (by omega), dif_pos (by omega)]
      have e2 : Formalism.BasicNotions.DV.sigPar D τ (i + 1) = -(D.hc τ).b ⟨i - (D.R.k - 1) + 1, by omega⟩ := by
        unfold Formalism.BasicNotions.DV.sigPar; rw [dif_neg (by omega), dif_pos (by omega)]
        congr 2; ext; simp; omega
      have g1 := (D.hc τ).gap_be ⟨i - (D.R.k - 1), by omega⟩
      have g2 := (D.hc τ).gap_eb ⟨i - (D.R.k - 1), by omega⟩ (by simp; omega)
      have ht : (0:ℚ) ≤ D.R.t := Nat.cast_nonneg _
      rw [e1, e2]
      have : (D.hc τ).b ⟨i - (D.R.k - 1), by omega⟩ + 1 ≤ (D.hc τ).b ⟨i - (D.R.k - 1) + 1, by omega⟩ := by
        linarith
      have : ((D.hc τ).b ⟨i - (D.R.k - 1), by omega⟩ : ℝ) + 1 ≤ ((D.hc τ).b ⟨i - (D.R.k - 1) + 1, by omega⟩ : ℝ) := by
        exact_mod_cast this
      push_cast
      linarith

theorem sigPar_anti (τ : D.what₂.Tau) (i : ℕ) :
    ∀ d : ℕ, i + d < D.R.k - 1 + D.R.m →
      (((Formalism.BasicNotions.DV.sigPar D τ (i + d) : ℚ) : ℝ)) + d ≤ ((Formalism.BasicNotions.DV.sigPar D τ i : ℚ) : ℝ) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := sigPar_step τ (i + d) (by omega)
    rw [show i + (d + 1) = i + d + 1 by ring]
    push_cast
    linarith

theorem log_const_poly_fifth_le (c : ℝ) (hc1 : 1 ≤ c) (hc2 : c ≤ 11) :
    Real.log (c * szPol L ^ 5 * L.sc.b) ≤ 16 * szPol L := by
  have hb := one_le_b L
  have hP := one_le_szPol L
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have lb : Real.log L.sc.b = L.sc.L := by unfold Scale.b; exact Real.log_exp _
  rw [lb]
  have l11 : Real.log c ≤ 10 := by have := Real.log_le_sub_one_of_pos (show (0:ℝ) < c by linarith); linarith
  have lP : Real.log (szPol L) ≤ szPol L := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have := L_le L
  push_cast
  nlinarith

theorem aPlus_arg (j : ℕ) (hj1 : 1 ≤ j) (ρ : D.what₂.Tau) (i : ℕ) :
    Formalism.BasicNotions.DV.aPlus D j ρ i + (((D.R.sigW j).1 : ℕ) : ℝ) - (i : ℝ) =
      ((Formalism.BasicNotions.DV.sigPar D ρ i : ℚ) : ℝ) + ((Formalism.BasicNotions.DV.eQ D j ρ : ℚ) : ℝ) - ((D.R.t : ℝ) - 1) / 2 := by
  have hnv := congrArg (fun q : ℚ => (q : ℝ)) (Formalism.BasicNotions.DV.nV_cast D.R)
  push_cast at hnv
  have hs : (((D.R.sigW j).1 : ℕ) : ℝ) = D.R.k + j - 1 := by
    show ((D.R.k + j - 1 : ℕ) : ℝ) = _
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hs]
  unfold Formalism.BasicNotions.DV.aPlus Formalism.BasicNotions.DV.aPlusQ
  push_cast
  rw [hnv]
  ring

theorem aPlus_diff (j : ℕ) (ρ : D.what₂.Tau) (i l : ℕ) :
    Formalism.BasicNotions.DV.aPlus D j ρ i - Formalism.BasicNotions.DV.aPlus D j ρ l + (l : ℝ) - (i : ℝ) =
      ((Formalism.BasicNotions.DV.sigPar D ρ i : ℚ) : ℝ) - ((Formalism.BasicNotions.DV.sigPar D ρ l : ℚ) : ℝ) := by
  unfold Formalism.BasicNotions.DV.aPlus Formalism.BasicNotions.DV.aPlusQ
  push_cast
  ring

theorem sigPar_at_last (ρ : D.what₂.Tau) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m) (hk : 1 ≤ D.R.k) :
    Formalism.BasicNotions.DV.sigPar D ρ (D.R.k + j - 2) = -(D.hc ρ).b ⟨j - 1, by omega⟩ := by
  unfold Formalism.BasicNotions.DV.sigPar
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 2; ext; simp; omega

theorem eQ_eq (ρ : D.what₂.Tau) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m) :
    Formalism.BasicNotions.DV.eQ D j ρ = (D.hc ρ).e ⟨j - 1, by omega⟩ := by
  unfold Formalism.BasicNotions.DV.eQ; rw [dif_pos ⟨hj1, hjm⟩]

theorem sigPar_abs (hN : SizeN L) (hK : SizeK L) (hLa : SizeLa L) (hBot : SizeBot L) (hEta : SizeEta L)
    (hDel : SizeDel L) (ρ : D.what₂.Tau) (i : ℕ) :
    |((Formalism.BasicNotions.DV.sigPar D ρ i : ℚ) : ℝ)| ≤ 5 * szPol L ^ 5 * L.sc.b := by
  have hb := one_le_b L
  have hP := one_le_szPol L
  have hPb := Pb_le (L := L) 5 (by norm_num)
  have hSc := Sc_le' hN hK hDel
  unfold Formalism.BasicNotions.DV.sigPar
  split_ifs with h1 h2
  · obtain ⟨v0, v1⟩ := L.cloud_v ρ ⟨i, h1⟩
    rw [abs_of_nonneg v0]; nlinarith
  · have := b_abs hN hK hLa hBot hEta ρ ⟨i - (D.R.k - 1), h2⟩
    push_cast; rw [abs_neg]; exact this
  · simp; positivity

theorem logHook_le (hN : SizeN L) (hK : SizeK L) (hLa : SizeLa L) (hBot : SizeBot L) (hEta : SizeEta L)
    (hDel : SizeDel L) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m) (ρ : D.what₂.Tau) :
    Formalism.BasicNotions.DV.logHook (D.R.sigW j).1 (Formalism.BasicNotions.DV.aPlus D j ρ) ≤ 160 * szPol L ^ 7 * L.sc.b := by
  have hk2 := k_two hK
  have hb := one_le_b L
  have hP := one_le_szPol L
  set Y : ℝ := 10 * szPol L ^ 5 * L.sc.b with hY
  have hY1 : 2 ≤ Y := by
    have : (1:ℝ) ≤ szPol L ^ 5 := one_le_pow₀ hP
    rw [hY]; nlinarith
  have hn : ((D.R.sigW j).1 : ℕ) = D.R.k + j - 1 := rfl
  obtain ⟨e0, e1⟩ := e_bounds hN hK hLa hBot hEta ρ ⟨j - 1, by omega⟩
  have gap := (D.hc ρ).gap_be ⟨j - 1, by omega⟩
  have gapR : ((D.R.t : ℝ) + 3) / 2 ≤ (((D.hc ρ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ) - (((D.hc ρ).b ⟨j - 1, by omega⟩ : ℚ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 gap; push_cast at this; linarith
  have hlast := sigPar_at_last ρ j hj1 hjm (by omega)
  have harg : ∀ i ∈ Finset.range ((D.R.sigW j).1),
      Real.log (Real.Gamma (Formalism.BasicNotions.DV.aPlus D j ρ i + (((D.R.sigW j).1 : ℕ) : ℝ) - (i : ℝ))) ≤ Y * Real.log Y := by
    intro i hi
    rw [Finset.mem_range, hn] at hi
    rw [aPlus_arg j hj1 ρ i, eQ_eq ρ j hj1 hjm]
    have ha := sigPar_anti ρ i (D.R.k + j - 2 - i) (by omega)
    rw [show i + (D.R.k + j - 2 - i) = D.R.k + j - 2 by omega, hlast] at ha
    push_cast at ha
    have hd : (0:ℝ) ≤ ((D.R.k + j - 2 - i : ℕ) : ℝ) := Nat.cast_nonneg _
    have hs := abs_le.1 (sigPar_abs hN hK hLa hBot hEta hDel ρ i)
    set y := ((Formalism.BasicNotions.DV.sigPar D ρ i : ℚ) : ℝ) + (((D.hc ρ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ) - ((D.R.t : ℝ) - 1) / 2 with hydef
    have hy2 : 2 ≤ y := by rw [hydef]; linarith
    have ht : (0:ℝ) ≤ D.R.t := Nat.cast_nonneg _
    have hyY : y ≤ Y := by
      have : (1:ℝ) ≤ szPol L ^ 5 * L.sc.b := by have : (1:ℝ) ≤ szPol L ^ 5 := one_le_pow₀ hP; nlinarith
      rw [hY, hydef]; linarith [hs.2]
    have l0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have l1 : Real.log y ≤ Real.log Y := Real.log_le_log (by linarith) hyY
    exact (logGamma_le y hy2).trans (mul_le_mul hyY l1 l0 (by linarith))
  have hden : ∀ i ∈ Finset.range ((D.R.sigW j).1), 0 ≤ ∑ l ∈ Finset.Ioo i ((D.R.sigW j).1),
      Real.log (Formalism.BasicNotions.DV.aPlus D j ρ i - Formalism.BasicNotions.DV.aPlus D j ρ l + l - i) := by
    intro i hi
    apply Finset.sum_nonneg
    intro l hl
    rw [Finset.mem_Ioo, hn] at hl
    rw [aPlus_diff]
    have ha := sigPar_anti ρ i (l - i) (by omega)
    rw [show i + (l - i) = l by omega] at ha
    have hd : (1:ℝ) ≤ ((l - i : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ l - i by omega)
    exact Real.log_nonneg (by linarith)
  unfold Formalism.BasicNotions.DV.logHook
  have s1 := Finset.sum_le_card_nsmul _ _ _ harg
  have s2 := Finset.sum_nonneg hden
  rw [Finset.card_range, nsmul_eq_mul] at s1
  have hnP : (((D.R.sigW j).1 : ℕ) : ℝ) ≤ szPol L := by
    rw [hn]
    refine le_trans ?_ (N_le L)
    have : D.R.k + j - 1 ≤ D.R.N D.R.m := by
      have : j ≤ D.R.m * (D.R.t + 1) := le_trans hjm (Nat.le_mul_of_pos_right _ (by omega))
      unfold Ranks.N; omega
    exact_mod_cast this
  have hlY := log_const_poly_fifth_le (L := L) 10 (by norm_num) (by norm_num)
  rw [← hY] at hlY
  have hlY0 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have e1 : Y * Real.log Y ≤ Y * (16 * szPol L) := mul_le_mul_of_nonneg_left hlY (by linarith)
  have e2 : (((D.R.sigW j).1 : ℕ) : ℝ) * (Y * Real.log Y) ≤ szPol L * (Y * (16 * szPol L)) :=
    mul_le_mul hnP e1 (by positivity) (by linarith)
  have e3 : szPol L * (Y * (16 * szPol L)) = 160 * szPol L ^ 7 * L.sc.b := by rw [hY]; ring
  linarith

theorem sum_card_le {ι : Type*} (s : Finset ι) (g : ι → ℝ) (B : ℝ) (hB : 0 ≤ B) (hs : (s.card : ℝ) ≤ szPol L)
    (h : ∀ i ∈ s, g i ≤ B) : ∑ i ∈ s, g i ≤ szPol L * B :=
  (Finset.sum_le_card_nsmul s g B h).trans (by rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hs hB)

theorem card_lifts : ((SizeData₂.lifts D).card : ℝ) ≤ szPol L := by
  have : (SizeData₂.lifts D).card = D.R.m := by unfold SizeData₂.lifts; simp
  rw [this]; exact m_le L

theorem card_Tau : ((Finset.univ : Finset D.what₂.Tau).card : ℝ) ≤ szPol L := by
  rw [Finset.card_univ, D.what₂.card_Tau]; exact f_le L

theorem card_TT (hTT : SizeTT L) : ((Finset.univ : Finset D.host.TT).card : ℝ) ≤ szPol L := by
  rw [Finset.card_univ, Fintype.card_coe]; exact TT_le hTT

theorem poly_pow_mul_b_le_ninth {a : ℕ} (ha : a ≤ 9) : szPol L ^ a * L.sc.b ≤ szPol L ^ 9 * L.sc.b :=
  mul_le_mul_of_nonneg_right (pow_mono_P ha) (by linarith [one_le_b L])

theorem sumT_le (hK : SizeK L) (hTT : SizeTT L) (CTu : ℝ)
    (hTu : ∀ u, Real.log ((D.mem u).A.T : ℝ) ≤ CTu * D.R.m * L.sc.L) (u : D.what₂.Word) :
    (∑ t : D.host.TT, (L.aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ)) ≤ 2 * |CTu| * szPol L ^ 9 * L.sc.b := by
  have hP := one_le_szPol L
  have hb := one_le_b L
  have hB : ∀ t ∈ (Finset.univ : Finset D.host.TT), (L.aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ) ≤
      2 * (szPol L * L.sc.b) * (|CTu| * szPol L * szPol L) := by
    intro t _
    obtain ⟨a0, a1⟩ := aT_bounds hK t
    have h1 : Real.log ((D.mem u).A.T : ℝ) ≤ |CTu| * szPol L * szPol L := by
      refine (hTu u).trans ?_
      have hm := m_le L; have hL := L_le L
      have hm0 : (0:ℝ) ≤ D.R.m := Nat.cast_nonneg _
      have hL0 := (sc_L_pos L).le
      have e1 : CTu * D.R.m * L.sc.L ≤ |CTu| * D.R.m * L.sc.L :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hm0) hL0
      have e2 : |CTu| * D.R.m * L.sc.L ≤ |CTu| * szPol L * szPol L := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hm (abs_nonneg _)) hL hL0 (by positivity)
      linarith
    rcases le_or_gt (Real.log ((D.mem u).A.T : ℝ)) 0 with hl | hl
    · have : (L.aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos a0 hl
      have : 0 ≤ 2 * (szPol L * L.sc.b) * (|CTu| * szPol L * szPol L) := by positivity
      linarith
    · exact mul_le_mul a1 h1 hl.le (by positivity)
  have s := sum_card_le (L := L) _ _ _ (by positivity) (card_TT hTT) hB
  have e : szPol L * (2 * (szPol L * L.sc.b) * (|CTu| * szPol L * szPol L)) = 2 * |CTu| * (szPol L ^ 4 * L.sc.b) := by ring
  have := poly_pow_mul_b_le_ninth (L := L) (a := 4) (by norm_num)
  have hc : 0 ≤ 2 * |CTu| := by positivity
  nlinarith

theorem negSZbP_le (hN : SizeN L) (hK : SizeK L) (hQD : SizeQD L) (hTT : SizeTT L) (hEta : SizeEta L)
    (hDel : SizeDel L) (CTu : ℝ) (hTu : ∀ u, Real.log ((D.mem u).A.T : ℝ) ≤ CTu * D.R.m * L.sc.L) (C : ℝ)
    (u : D.what₂.Word) :
    -Formalism.BasicNotions.DV.SZbP D L C u ≤ (2 * |CTu| + 16 * |C|) * szPol L ^ 9 * L.sc.b := by
  have hP := one_le_szPol L
  have hb := one_le_b L
  have hs := sumT_le hK hTT CTu hTu u
  obtain ⟨La0, La1⟩ := La_bounds hN hK hQD
  set Q : ℝ := (D.host.TT.card : ℝ) * L.sc.b' * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * ((D.R.m : ℝ) * L.etaSz + L.Sc) * (D.R.N D.R.m : ℝ) + (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 with hQ
  have hb' := b'_nonneg L
  have he0 := L.etaSz_pos.le
  have hSc0 := L.Sc_pos.le
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hTTP := TT_le hTT
  have hb'P : L.sc.b' ≤ szPol L * L.sc.b := (b'_le_a L).trans (a_le L hK)
  have hNP := N_le L; have hfP := f_le L; have hmP := m_le L
  have heta := eta_le hN hK hEta
  have hScP := Sc_le' hN hK hDel
  have hQle : Q ≤ 4 * szPol L ^ 3 * L.sc.b := by
    have t1 : (D.host.TT.card : ℝ) * L.sc.b' * (D.R.N D.R.m : ℝ) ≤ szPol L * (szPol L * L.sc.b) * szPol L := by
      gcongr
    have t2 : (D.R.f : ℝ) * ((D.R.m : ℝ) * L.etaSz + L.Sc) * (D.R.N D.R.m : ℝ) ≤
        szPol L * (szPol L * L.sc.b + szPol L * L.sc.b) * szPol L := by
      gcongr
    have t3 : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 ≤ szPol L * szPol L ^ 2 := by gcongr
    have t4 : szPol L * szPol L ^ 2 ≤ szPol L ^ 3 * L.sc.b := by
      have : 0 ≤ szPol L ^ 3 := by positivity
      nlinarith
    rw [hQ]; nlinarith
  have key : -(C * Q * L.La) ≤ |C| * (4 * szPol L ^ 3 * L.sc.b) * (4 * szPol L) := by
    calc -(C * Q * L.La) ≤ |C * Q * L.La| := neg_le_abs _
      _ = |C| * Q * L.La := by rw [abs_mul, abs_mul, abs_of_nonneg hQ0, abs_of_nonneg La0]
      _ ≤ |C| * (4 * szPol L ^ 3 * L.sc.b) * (4 * szPol L) := by gcongr
  have e : |C| * (4 * szPol L ^ 3 * L.sc.b) * (4 * szPol L) = 16 * |C| * (szPol L ^ 4 * L.sc.b) := by ring
  have := poly_pow_mul_b_le_ninth (L := L) (a := 4) (by norm_num)
  have hc : 0 ≤ 16 * |C| := by positivity
  unfold Formalism.BasicNotions.DV.SZbP
  rw [← hQ]
  nlinarith

theorem neg_size_term_le_poly_eighth (P5 : ParameterChoice' D L) (hN : SizeN L) (hK : SizeK L) (hQD : SizeQD L) (hLa : SizeLa L)
    (hBot : SizeBot L) (hEta : SizeEta L) (hDel : SizeDel L) (C : ℝ) (u : D.what₂.Word) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) :
    -Formalism.BasicNotions.DV.kernelPlaceMeanBound D L C u j ≤ 300 * szPol L ^ 8 * L.sc.b + 5 * |C| * szPol L ^ 8 * L.sc.b := by
  have hjm : j ≤ D.R.m := (Finset.mem_Icc.1 hj).2
  have hP := one_le_szPol L
  have hb := one_le_b L
  obtain ⟨La0, La1⟩ := La_bounds hN hK hQD
  have hk : ∀ ρ ∈ (Finset.univ : Finset D.what₂.Tau), -Formalism.BasicNotions.DV.kerPlace D L u j ρ ≤ 300 * szPol L ^ 7 * L.sc.b :=
    fun ρ _ => by linarith [kerPlace_lower P5 hN hK hQD hLa hBot hEta hDel u j hjm ρ]
  have s := sum_card_le (L := L) _ _ _ (by positivity) (card_Tau (L := L)) hk
  rw [Finset.sum_neg_distrib] at s
  have hNP := N_le L; have hfP := f_le L; have hmP := m_le L; have hLP := L_le L
  have hL0 := (sc_L_pos L).le
  have q1 : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La ≤ szPol L * szPol L ^ 2 * (4 * szPol L) := by gcongr
  have q2 : (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * L.sc.L ≤
      szPol L * szPol L ^ 3 * szPol L ^ 2 * szPol L := by gcongr
  have a1 : -(C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La) ≤ |C| * (szPol L * szPol L ^ 2 * (4 * szPol L)) := by
    have q0 : 0 ≤ (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La := mul_nonneg (by positivity) La0
    calc _ = -(C * ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La)) := by ring
      _ ≤ |C * ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La)| := neg_le_abs _
      _ = |C| * ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La) := by rw [abs_mul, abs_of_nonneg q0]
      _ ≤ _ := mul_le_mul_of_nonneg_left q1 (abs_nonneg _)
  have a2 : -(C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * L.sc.L) ≤
      |C| * (szPol L * szPol L ^ 3 * szPol L ^ 2 * szPol L) := by
    have q0 : 0 ≤ (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * L.sc.L := mul_nonneg (by positivity) hL0
    calc _ = -(C * ((D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * L.sc.L)) := by ring
      _ ≤ |C * ((D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * L.sc.L)| := neg_le_abs _
      _ = |C| * ((D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * L.sc.L) := by rw [abs_mul, abs_of_nonneg q0]
      _ ≤ _ := mul_le_mul_of_nonneg_left q2 (abs_nonneg _)
  have e1 : szPol L * (300 * szPol L ^ 7 * L.sc.b) = 300 * szPol L ^ 8 * L.sc.b := by ring
  have e2 : szPol L * szPol L ^ 2 * (4 * szPol L) = 4 * szPol L ^ 4 := by ring
  have e3 : szPol L * szPol L ^ 3 * szPol L ^ 2 * szPol L = szPol L ^ 7 := by ring
  have p4 : szPol L ^ 4 ≤ szPol L ^ 8 * L.sc.b := by
    have := pow_mono_P (L := L) (a := 4) (b := 8) (by norm_num)
    have : 0 ≤ szPol L ^ 8 := by positivity
    nlinarith
  have p7 : szPol L ^ 7 ≤ szPol L ^ 8 * L.sc.b := by
    have := pow_mono_P (L := L) (a := 7) (b := 8) (by norm_num)
    have : 0 ≤ szPol L ^ 8 := by positivity
    nlinarith
  have hC := abs_nonneg C
  unfold Formalism.BasicNotions.DV.kernelPlaceMeanBound
  rw [e2] at a1; rw [e3] at a2
  nlinarith

theorem L6lo_le (hN : SizeN L) (hK : SizeK L) (hQD : SizeQD L) (hLa : SizeLa L) (hBot : SizeBot L)
    (hEta : SizeEta L) (hDel : SizeDel L) (hG : SizeG L) (C : ℝ) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    Formalism.BasicNotions.DV.L6lo D L C j ≤ 160 * szPol L ^ 8 * L.sc.b + 6 * |C| * szPol L ^ 8 * L.sc.b := by
  have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
  have hjm : j ≤ D.R.m := (Finset.mem_Icc.1 hj).2
  have hP := one_le_szPol L
  have hb := one_le_b L
  have hk : ∀ ρ ∈ (Finset.univ : Finset D.what₂.Tau),
      Formalism.BasicNotions.DV.logHook (D.R.sigW j).1 (Formalism.BasicNotions.DV.aPlus D j ρ) ≤ 160 * szPol L ^ 7 * L.sc.b :=
    fun ρ _ => logHook_le hN hK hLa hBot hEta hDel j hj1 hjm ρ
  have s := sum_card_le (L := L) _ _ _ (by positivity) (card_Tau (L := L)) hk
  obtain ⟨Lp0, Lp1⟩ := Lprime_bounds hN hK hQD hG
  have hfP := f_le L; have hvP := nV_le L
  have q : (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Formalism.BasicNotions.DV.Lprime D L ≤ szPol L * szPol L ^ 2 * (6 * szPol L ^ 2) := by
    gcongr
  have a1 : -(C * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Formalism.BasicNotions.DV.Lprime D L) ≤ |C| * (szPol L * szPol L ^ 2 * (6 * szPol L ^ 2)) := by
    have q0 : 0 ≤ (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Formalism.BasicNotions.DV.Lprime D L := mul_nonneg (by positivity) Lp0
    calc _ = -(C * ((D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Formalism.BasicNotions.DV.Lprime D L)) := by ring
      _ ≤ |C * ((D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Formalism.BasicNotions.DV.Lprime D L)| := neg_le_abs _
      _ = |C| * ((D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Formalism.BasicNotions.DV.Lprime D L) := by rw [abs_mul, abs_of_nonneg q0]
      _ ≤ _ := mul_le_mul_of_nonneg_left q (abs_nonneg _)
  have e1 : szPol L * (160 * szPol L ^ 7 * L.sc.b) = 160 * szPol L ^ 8 * L.sc.b := by ring
  have e2 : szPol L * szPol L ^ 2 * (6 * szPol L ^ 2) = 6 * szPol L ^ 5 := by ring
  have p5 : szPol L ^ 5 ≤ szPol L ^ 8 * L.sc.b := by
    have := pow_mono_P (L := L) (a := 5) (b := 8) (by norm_num)
    have : 0 ≤ szPol L ^ 8 := by positivity
    nlinarith
  have hC := abs_nonneg C
  unfold Formalism.BasicNotions.DV.L6lo
  rw [e2] at a1
  nlinarith

theorem _root_.Formalism.MainNotions.DIV.Proofs.hExpl6_lower_at (P5 : ParameterChoice' D L) (hS : SizesAt L) (CTu : ℝ)
    (hTu : ∀ u, Real.log ((D.mem u).A.T : ℝ) ≤ CTu * D.R.m * L.sc.L) (X : DivX D) (C : ℝ) (u : D.what₂.Word) :
    -(Formalism.BasicNotions.DV.hExpl6 D L X C u + Formalism.BasicNotions.DV.meanE D (fun e => Real.log (X.kapR e))) ≤
      (500 + 2 * |CTu| + 30 * |C|) * szPol L ^ 9 * L.sc.b := by
  obtain ⟨hN, -, hK, -, -, -, hQD, hTT, hLa, -, hBot, -, -, hEta, -, -, hDel, -, -, -, hG, -, -⟩ := hS
  have hP := one_le_szPol L
  have hb := one_le_b L
  have t1 := negSZbP_le hN hK hQD hTT hEta hDel CTu hTu C u
  have t2 : ∑ j ∈ SizeData₂.lifts D, -Formalism.BasicNotions.DV.kernelPlaceMeanBound D L C u j ≤
      szPol L * (300 * szPol L ^ 8 * L.sc.b + 5 * |C| * szPol L ^ 8 * L.sc.b) :=
    sum_card_le (L := L) _ _ _ (by positivity) (card_lifts (L := L))
      fun j hj => neg_size_term_le_poly_eighth P5 hN hK hQD hLa hBot hEta hDel C u j hj
  have t3 : ∑ j ∈ SizeData₂.lifts D, Formalism.BasicNotions.DV.L6lo D L C j ≤
      szPol L * (160 * szPol L ^ 8 * L.sc.b + 6 * |C| * szPol L ^ 8 * L.sc.b) :=
    sum_card_le (L := L) _ _ _ (by positivity) (card_lifts (L := L))
      fun j hj => L6lo_le hN hK hQD hLa hBot hEta hDel hG C j hj
  rw [Finset.sum_neg_distrib] at t2
  have e : Formalism.BasicNotions.DV.hExpl6 D L X C u + Formalism.BasicNotions.DV.meanE D (fun e => Real.log (X.kapR e)) =
      Formalism.BasicNotions.DV.SZbP D L C u + (∑ j ∈ SizeData₂.lifts D, Formalism.BasicNotions.DV.kernelPlaceMeanBound D L C u j) -
        (∑ j ∈ SizeData₂.lifts D, Formalism.BasicNotions.DV.L6lo D L C j) := by
    unfold Formalism.BasicNotions.DV.hExpl6; ring
  rw [e]
  have e2 : szPol L * (300 * szPol L ^ 8 * L.sc.b + 5 * |C| * szPol L ^ 8 * L.sc.b) =
      (300 + 5 * |C|) * szPol L ^ 9 * L.sc.b := by ring
  have e3 : szPol L * (160 * szPol L ^ 8 * L.sc.b + 6 * |C| * szPol L ^ 8 * L.sc.b) =
      (160 + 6 * |C|) * szPol L ^ 9 * L.sc.b := by ring
  rw [e2] at t2; rw [e3] at t3
  have hC := abs_nonneg C
  have h9 : 0 ≤ szPol L ^ 9 * L.sc.b := by positivity
  nlinarith

theorem _root_.Formalism.MainNotions.DIV.Proofs.szPol_le_rpow (hS : SizesAt L) (hx : 9 ≤ L.sc.x) : szPol L ≤ L.sc.x ^ (max L.Ct 5 + 3) := by
  obtain ⟨hN, hM, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hS
  have hx0 : 0 < L.sc.x := sc_x_pos L
  have hx1 : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have he := L.sc.eps_pos
  have he' := L.sc.eps_lt
  set c := max L.Ct 5 with hc
  have hc5 : 5 ≤ c := le_max_right _ _
  have hct : L.Ct ≤ c := le_max_left _ _
  have rp : ∀ a b : ℝ, a ≤ b → L.sc.x ^ a ≤ L.sc.x ^ b := fun a b h => Real.rpow_le_rpow_of_exponent_le hx1 h
  set X := L.sc.x ^ (c + 2) with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hx1 (by linarith)
  have hth : szTh L ≤ L.sc.eps / 100 := le_refl _
  have hth0 : 0 ≤ szTh L := by unfold szTh; linarith
  have hxx : ∀ a b : ℝ, L.sc.x ^ a * L.sc.x ^ b = L.sc.x ^ (a + b) := fun a b => (Real.rpow_add hx0 a b).symm

  have hf : (D.R.f : ℝ) ≤ X := by
    rw [f_eq]
    have h1 : 2 * (D.R.n : ℝ) ≤ L.sc.x ^ (1:ℝ) * L.sc.x ^ (2 + 8 * L.sc.eps + szTh L) := by
      rw [Real.rpow_one]; nlinarith [hN.2]
    rw [hxx] at h1
    exact h1.trans (rp _ _ (by unfold szTh at *; linarith))
  have hk : (D.R.k : ℝ) ≤ X := hK.2.trans (rp _ _ (by unfold szTh at *; linarith))
  have hm : (D.R.m : ℝ) ≤ L.sc.x ^ (szTh L + 1 / 2) := by
    refine hM.2.trans ?_
    have hs : Real.sqrt (L.sc.x * L.sc.delta1) ≤ L.sc.x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.sqrt_le_sqrt
      have := delta1_le (L := L)
      nlinarith
    rw [← hxx]
    exact mul_le_mul_of_nonneg_left hs (Real.rpow_pos_of_pos hx0 _).le
  have hmX : (D.R.m : ℝ) ≤ X := hm.trans (rp _ _ (by unfold szTh at *; linarith))
  have ht : (D.R.t : ℝ) ≤ L.sc.x ^ c := L.t_win.2.trans (rp _ _ hct)
  have htX : (D.R.t : ℝ) ≤ X := ht.trans (rp _ _ (by linarith))
  have hxc1 : 1 ≤ L.sc.x ^ c := Real.one_le_rpow hx1 (by linarith)
  have hNX : (D.R.N D.R.m : ℝ) ≤ 2 * X := by
    have hNe : (D.R.N D.R.m : ℝ) = D.R.k + D.R.m * (D.R.t + 1) := by unfold Ranks.N; push_cast; ring
    have h1 : (D.R.t : ℝ) + 1 ≤ L.sc.x ^ (1:ℝ) * L.sc.x ^ c := by rw [Real.rpow_one]; nlinarith
    rw [hxx] at h1
    have h2 : (D.R.m : ℝ) * (D.R.t + 1) ≤ L.sc.x ^ (szTh L + 1 / 2) * L.sc.x ^ (1 + c) :=
      mul_le_mul hm h1 (by positivity) (Real.rpow_pos_of_pos hx0 _).le
    rw [hxx] at h2
    have h3 : L.sc.x ^ (szTh L + 1 / 2 + (1 + c)) ≤ X := rp _ _ (by unfold szTh at *; linarith)
    rw [hNe]; linarith
  have hL : L.sc.L ≤ X := rp _ _ (by linarith)
  have hsum : szPol L ≤ 8 * X := by unfold szPol; linarith
  have h8 : 8 * X ≤ L.sc.x ^ (1:ℝ) * X := by rw [Real.rpow_one]; nlinarith
  rw [hX, hxx] at h8
  rw [hX] at hsum
  exact hsum.trans (h8.trans (le_of_eq (by ring_nf)))

theorem _root_.Formalism.MainNotions.DIV.Proofs.bPol_le (hS : SizesAt L) (C : ℝ) (e : ℕ) (hx : max 9 C ≤ L.sc.x) :
    C * szPol L ^ e * L.sc.b ≤ L.sc.x ^ ((e : ℝ) * (max L.Ct 5 + 3) + 1) * L.sc.b := by
  have hx0 : 0 < L.sc.x := sc_x_pos L
  have hx9 : 9 ≤ L.sc.x := (le_max_left _ _).trans hx
  have hxC : C ≤ L.sc.x := (le_max_right _ _).trans hx
  have hp := szPol_le_rpow hS hx9
  have hP := one_le_szPol L
  have hb := one_le_b L
  have h1 : szPol L ^ e ≤ L.sc.x ^ ((e : ℝ) * (max L.Ct 5 + 3)) := by
    calc szPol L ^ e ≤ (L.sc.x ^ (max L.Ct 5 + 3)) ^ e := pow_le_pow_left₀ (by linarith) hp e
      _ = L.sc.x ^ ((e : ℝ) * (max L.Ct 5 + 3)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, mul_comm]
  have h2 : C * szPol L ^ e ≤ L.sc.x * szPol L ^ e := mul_le_mul_of_nonneg_right hxC (by positivity)
  have h3 : L.sc.x * szPol L ^ e ≤ L.sc.x * L.sc.x ^ ((e : ℝ) * (max L.Ct 5 + 3)) :=
    mul_le_mul_of_nonneg_left h1 hx0.le
  have h4 : L.sc.x * L.sc.x ^ ((e : ℝ) * (max L.Ct 5 + 3)) = L.sc.x ^ ((e : ℝ) * (max L.Ct 5 + 3) + 1) := by
    rw [Real.rpow_add hx0, Real.rpow_one, mul_comm]
  exact mul_le_mul_of_nonneg_right (h2.trans (h3.trans h4.le)) (by linarith)

theorem _root_.Formalism.MainNotions.DIV.Proofs.hExpl6_lower {eps : ℝ} (Fm : FamP eps) (hTu : TuSize Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word),
      -(Formalism.BasicNotions.DV.hExpl6 (Fm.D x i) (Fm.L x i) (Fm.X x i) Fm.Csz u +
          Formalism.BasicNotions.DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e))) ≤
        (500 + 2 * |Fm.CTu| + 30 * |Fm.Csz|) * szPol (Fm.L x i) ^ 9 * (Fm.L x i).sc.b := by
  obtain ⟨x0, h0⟩ := hTu
  exact ⟨x0, fun x hx hx1 i u => hExpl6_lower_at (Fm.params x hx1 i) (Fm.sizes x hx1 i) Fm.CTu
    (h0 x hx i).2 (Fm.X x i) Fm.Csz u⟩

theorem _root_.Formalism.MainNotions.DIV.Proofs.hExpl6_lower_pow {eps : ℝ} (Fm : FamP eps) (hTu : TuSize Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word),
      -(Formalism.BasicNotions.DV.hExpl6 (Fm.D x i) (Fm.L x i) (Fm.X x i) Fm.Csz u +
          Formalism.BasicNotions.DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e))) ≤
        x ^ (9 * (max Fm.Ct 5 + 3) + 1) * (Fm.L x i).sc.b := by
  obtain ⟨x0, h0⟩ := hExpl6_lower Fm hTu
  refine ⟨max x0 (max 9 (500 + 2 * |Fm.CTu| + 30 * |Fm.Csz|)), fun x hx hx1 i u => ?_⟩
  have hsc : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hCt : (Fm.L x i).Ct = Fm.Ct := Fm.Ct_eq x i
  have h1 := h0 x ((le_max_left _ _).trans hx) hx1 i u
  have h2 := bPol_le (Fm.sizes x hx1 i) (500 + 2 * |Fm.CTu| + 30 * |Fm.Csz|) 9
    (by rw [hsc]; exact (le_max_right _ _).trans hx)
  rw [hsc, hCt] at h2
  norm_num at h2
  linarith

theorem _root_.Formalism.MainNotions.DIV.Proofs.const_rank_base_le_poly_fourth (C : ℝ) : C * D.R.m * L.B0 ≤ |C| * szPol L ^ 4 * L.sc.b := by
  have hB : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L := rfl
  have hP := one_le_szPol L
  have hb := one_le_b L
  have hL0 := (sc_L_pos L).le
  have q : (D.R.m : ℝ) * ((D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L) ≤ szPol L * (szPol L * szPol L * L.sc.b * szPol L) := by
    have := f_le L; have := m_le L; have := L_le L
    gcongr
  have q0 : 0 ≤ (D.R.m : ℝ) * ((D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L) := by positivity
  rw [hB]
  calc C * D.R.m * ((D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L)
      = C * ((D.R.m : ℝ) * ((D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L)) := by ring
    _ ≤ |C| * ((D.R.m : ℝ) * ((D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L)) := mul_le_mul_of_nonneg_right (le_abs_self _) q0
    _ ≤ |C| * (szPol L * (szPol L * szPol L * L.sc.b * szPol L)) := mul_le_mul_of_nonneg_left q (abs_nonneg _)
    _ = |C| * szPol L ^ 4 * L.sc.b := by ring

end Formalism.MainNotions.DIV.Proofs.HHParts

end
