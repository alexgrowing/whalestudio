import Formalism.SharpRestriction.Divisibility.HookProducts.AbsPhFSubLeOfLe
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ElevenLe

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.RBCompl3

open Formalism.BasicNotions

theorem wSz_eq_wj (D : D7) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) : DV.wSz D (i + 1) τ = wj D (i + 1) τ := by
  unfold DV.wSz wj
  rw [dif_pos ⟨by omega, by omega⟩, dif_pos (by omega)]

theorem compl3_diff (D : D7) (L : SizeData₂ D) (Z : DivX D) (Csz : ℝ) (u u' : D.what₂.Word) :
    (DV.hExpl6 D L Z Csz u + (∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log ((D.mem u).A.T : ℝ)) -
      (DV.hExpl6 D L Z Csz u' + (∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log ((D.mem u').A.T : ℝ)) =
    ∑ j ∈ SizeData₂.lifts D, ∑ τ : D.what₂.Tau, (DV.kerPlace D L u j τ - DV.kerPlace D L u' j τ) := by
  unfold DV.hExpl6 DV.SZbP DV.kernelPlaceMeanBound
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul]
  ring

theorem compl3_abs_le (D : D7) (L : SizeData₂ D) (Z : DivX D) (Csz M : ℝ) (hM1 : 1 ≤ M)
    (hM : ∀ i < D.R.m, ∀ τ : D.what₂.Tau, L.Sc + wj D (i + 1) τ ≤ M) (u u' : D.what₂.Word) :
    |(DV.hExpl6 D L Z Csz u + (∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log ((D.mem u).A.T : ℝ)) -
      (DV.hExpl6 D L Z Csz u' + (∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log ((D.mem u').A.T : ℝ))| ≤
      (D.R.m : ℝ) * ((D.R.f : ℝ) * ((D.R.k : ℝ) * (L.Sc * (Real.log M + |L.logOm|)))) := by
  rw [compl3_diff]
  calc _ ≤ ∑ j ∈ SizeData₂.lifts D, |∑ τ : D.what₂.Tau, (DV.kerPlace D L u j τ - DV.kerPlace D L u' j τ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ SizeData₂.lifts D, ∑ τ : D.what₂.Tau, |DV.kerPlace D L u j τ - DV.kerPlace D L u' j τ| :=
        Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ SizeData₂.lifts D, ∑ τ : D.what₂.Tau, (D.R.k : ℝ) * (L.Sc * (Real.log M + |L.logOm|)) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro τ _
        have hj' : 1 ≤ j ∧ j ≤ D.R.m := by simpa [SizeData₂.lifts] using hj
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have hi : i < D.R.m := by omega
        exact abs_kerPlace_sub_le D L u u' i hi τ M hM1 (by rw [wSz_eq_wj D i hi τ]; exact hM i hi τ)
    _ = (D.R.m : ℝ) * ((D.R.f : ℝ) * ((D.R.k : ℝ) * (L.Sc * (Real.log M + |L.logOm|)))) := by
        simp only [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, SizeData₂.lifts, Nat.card_Icc,
          Nat.add_sub_cancel, nsmul_eq_mul]

theorem sc_add_wj_le (D : D7) (L : SizeData₂ D) (S : SizesAt L) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    L.Sc + wj D (i + 1) τ ≤ 6 * L.sc.x ^ 6 * L.sc.b := by
  obtain ⟨hN, hMm, hK, hKR, hT, hCond, hQD, hTT, hLa, hRho, hBot, hDe2, hLw, hEta, hNodes, hLstar, hDel, hW, hBm,
    hXpp, hG, hPde, hWords⟩ := S
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have heps := L.sc.eps_pos
  have hepsl := L.sc.eps_lt
  have hL0 : 0 < L.sc.L := Real.rpow_pos_of_pos hx0 _
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp hL0.le
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hn0 : (0 : ℝ) < D.R.n := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hN.1
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 0 < D.R.n := by exact_mod_cast hn0
    exact_mod_cast this
  have hX'1 : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_pos_of_pos hx0 _).le
  have hb' : L.sc.b' ≤ L.sc.x * L.sc.b := by
    unfold Scale.b' Scale.a
    exact div_le_self (by positivity) hX'1
  have hb'0 : 0 ≤ L.sc.b' := by unfold Scale.b' Scale.a Scale.X'; positivity
  have hw'' : L.sc.w'' D.R.n ≤ L.sc.b := by
    unfold Scale.w''
    rw [div_le_iff₀ (by positivity)]
    calc L.sc.b' ≤ L.sc.x * L.sc.b := hb'
      _ ≤ L.sc.x * L.sc.b * D.R.n := le_mul_of_one_le_right (by positivity) hn1
      _ = L.sc.b * (L.sc.x * D.R.n) := by ring
  have hkSc : (D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n := hDel.2.2.2.1
  have hSc0 : 0 ≤ L.Sc := L.Sc_pos.le
  have hSc : L.Sc ≤ L.sc.b := by
    have : L.Sc ≤ (D.R.k : ℝ) * L.Sc := le_mul_of_one_le_left hSc0 hk1
    linarith
  have hw''0 : 0 ≤ L.sc.w'' D.R.n := le_trans (by positivity) hkSc
  have hEta0 : 0 ≤ L.etaSz := L.etaSz_pos.le
  have heta : L.etaSz ≤ L.sc.b := by
    have h1 : L.etaSz ≤ (D.R.t : ℝ) * L.etaSz := le_mul_of_one_le_left hEta0 hT.1
    have h2 : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.w'' D.R.n := div_le_self hw''0 hx1.le
    linarith [hEta.2.2.2.1]
  have hx6 : 1 ≤ L.sc.x ^ 6 := one_le_pow₀ hx1.le
  have hxx6 : L.sc.x ≤ L.sc.x ^ 6 := by
    calc L.sc.x = L.sc.x ^ 1 := (pow_one _).symm
      _ ≤ L.sc.x ^ 6 := pow_le_pow_right₀ hx1.le (by norm_num)
  have hj1 : 1 ≤ i + 1 := by omega
  have hjm : i + 1 ≤ D.R.m := by omega
  by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · simp only [Host.topPlaces, Finset.mem_image] at htop
    obtain ⟨a, ha, hae⟩ := htop
    have hw := L.win_top (i + 1) hj1 hjm τ ⟨a, ha⟩ hae.symm
    have hbt := hBot ⟨a, ha⟩

    have hd1 : L.sc.delta1 ≤ 1 := by
      unfold Scale.delta1
      exact Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
    have hd0 : 0 ≤ L.sc.delta1 := by unfold Scale.delta1; positivity
    have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ 3 := by
      have h := hN.2
      have h2 : L.sc.x ^ (2 + 8 * L.sc.eps + szTh L) ≤ L.sc.x ^ ((3 : ℕ) : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hx1.le
        unfold szTh
        push_cast
        linarith
      rw [Real.rpow_natCast] at h2
      linarith
    have hxe : L.sc.x ^ L.sc.eps ≤ L.sc.x := by
      calc L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
        _ = L.sc.x := Real.rpow_one _
    have hLaG : L.LaG ≤ L.sc.x := by
      calc L.LaG ≤ L.sc.x ^ (L.sc.eps + szTh L) := hLa.2
        _ ≤ L.sc.x ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hx1.le
          unfold szTh
          linarith
        _ = L.sc.x := Real.rpow_one _
    have hLaG0 : 0 ≤ L.LaG := le_trans (Real.rpow_pos_of_pos hx0 _).le hLa.1
    have hNst : szNst L ≤ 2 * L.sc.x ^ 3 := by
      unfold szNst
      have : (D.R.n : ℝ) * L.sc.delta1 ≤ L.sc.x ^ 3 * 1 :=
        mul_le_mul hn3 hd1 hd0 (by positivity)
      linarith
    have hNst0 : 0 ≤ szNst L := by unfold szNst; positivity
    have hP : szNst L * L.sc.x ^ L.sc.eps * L.LaG ≤ 2 * L.sc.x ^ 5 := by
      have h1 : szNst L * L.sc.x ^ L.sc.eps ≤ 2 * L.sc.x ^ 3 * L.sc.x :=
        mul_le_mul hNst hxe (by positivity) (by positivity)
      have h2 : szNst L * L.sc.x ^ L.sc.eps * L.LaG ≤ 2 * L.sc.x ^ 3 * L.sc.x * L.sc.x :=
        mul_le_mul h1 hLaG hLaG0 (by positivity)
      calc _ ≤ 2 * L.sc.x ^ 3 * L.sc.x * L.sc.x := h2
        _ = 2 * L.sc.x ^ 5 := by ring
    have hq : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k ≤ 2 * L.sc.x ^ 5 * (L.sc.x * L.sc.b) := by
      rw [div_le_iff₀ (by linarith)]
      have h0 : 0 ≤ szNst L * L.sc.x ^ L.sc.eps * L.LaG := by positivity
      calc szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' ≤ 2 * L.sc.x ^ 5 * (L.sc.x * L.sc.b) :=
            mul_le_mul hP hb' hb'0 (by positivity)
        _ ≤ 2 * L.sc.x ^ 5 * (L.sc.x * L.sc.b) * D.R.k := le_mul_of_one_le_right (by positivity) hk1
    have hbx : L.sc.b' / L.sc.x ≤ L.sc.b := by
      rw [div_le_iff₀ hx0]; linarith
    have hfin : L.sc.x ^ 5 * (L.sc.x * L.sc.b) = L.sc.x ^ 6 * L.sc.b := by ring
    have hxb : L.sc.x * L.sc.b ≤ L.sc.x ^ 6 * L.sc.b := mul_le_mul_of_nonneg_right hxx6 (by positivity)
    have hbb : L.sc.b ≤ L.sc.x ^ 6 * L.sc.b := le_mul_of_one_le_left (by positivity) hx6
    linarith [hw.2, hbt, hq, hfin, hb', hxb, hbx, heta, hbb, hSc]
  · by_cases hthick : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have hw := L.win_thick (i + 1) hj1 hjm τ hthick
      have hbb : L.sc.b ≤ L.sc.x ^ 6 * L.sc.b := le_mul_of_one_le_left (by positivity) hx6
      linarith [hw.2]
    · have hthin : D.host.IsThin (D.eTau τ : D.R.GG) := ⟨(D.eTau τ).2, htop, hthick⟩
      have hw := L.win_thin (i + 1) hj1 hjm τ hthin
      have hbb : L.sc.b ≤ L.sc.x ^ 6 * L.sc.b := le_mul_of_one_le_left (by positivity) hx6
      linarith [hw.2]

theorem kSc_le_b (D : D7) (L : SizeData₂ D) (S : SizesAt L) : (D.R.k : ℝ) * L.Sc ≤ L.sc.b := by
  obtain ⟨hN, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hDel, _⟩ := S
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hn0 : (0 : ℝ) < D.R.n := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hN.1
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 0 < D.R.n := by exact_mod_cast hn0
    exact_mod_cast this
  have hX'1 : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_pos_of_pos hx0 _).le
  have hbpos : 0 < L.sc.b := Real.exp_pos _
  have hb' : L.sc.b' ≤ L.sc.x * L.sc.b := by
    unfold Scale.b' Scale.a
    exact div_le_self (by positivity) hX'1
  have hw'' : L.sc.w'' D.R.n ≤ L.sc.b := by
    unfold Scale.w''
    rw [div_le_iff₀ (by positivity)]
    calc L.sc.b' ≤ L.sc.x * L.sc.b := hb'
      _ ≤ L.sc.x * L.sc.b * D.R.n := le_mul_of_one_le_right (by positivity) hn1
      _ = L.sc.b * (L.sc.x * D.R.n) := by ring
  exact le_trans hDel.2.2.2.1 hw''

theorem abs_logOm_le (D : D7) (L : SizeData₂ D) (S : SizesAt L) (P : ParameterChoice' D L) :
    |L.logOm| ≤ 6 + 2 * L.sc.L := by
  obtain ⟨_, _, _, _, _, _, hQD, _⟩ := S
  have hrd : 1 ≤ D.host.rdE := hQD.2.2.2.2.2.2.1
  have hdl : |L.logDerivativeAtOne| ≤ L.sc.L := hQD.2.2.2.2.2.1
  have hlrd : Real.log D.host.rdE ≤ L.sc.L := log_rdE_le_scL P
  have hlrd0 : 0 ≤ Real.log D.host.rdE := Real.log_nonneg hrd
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hlpi : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos hpi0
    linarith [Real.pi_le_four]
  have hlpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hg1 := Real.eulerMascheroniConstant_lt_two_thirds
  have hg0 := Real.one_half_lt_eulerMascheroniConstant
  have hv : Real.log (Real.pi / D.host.v) = Real.log Real.pi - Real.log D.host.rdE + Real.log 2 := by
    unfold Host.v
    rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by norm_num)]
    ring
  unfold SizeData₂.logOm
  rw [hv, abs_le]
  have hd := abs_le.1 hdl
  constructor <;> linarith [hd.1, hd.2]

theorem log_M_le (L : Scale) : Real.log (6 * L.x ^ 6 * L.b) ≤ 5 + 6 * (L.L / L.eps) + L.L := by
  have hx0 : 0 < L.x := by linarith [L.one_lt_alt]
  have hb : L.b = Real.exp L.L := rfl
  rw [Real.log_mul (by positivity) (by rw [hb]; positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_pow, hb, Real.log_exp]
  have h6 : Real.log 6 ≤ 5 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
    linarith
  have hlx : Real.log L.x ≤ L.x ^ L.eps / L.eps := Real.log_le_rpow_div hx0.le L.eps_pos
  have hL : L.L = L.x ^ L.eps := rfl
  rw [← hL] at hlx
  push_cast
  linarith

theorem compl3_record (D : D7) (L : SizeData₂ D) (Z : DivX D) (Csz : ℝ) (P : ParameterChoice' D L) (S : SizesAt L) :
    Formalism.L2.DIV.Compl3 L Z Csz (20 + 6 / L.sc.eps) := by
  unfold Formalism.L2.DIV.Compl3
  intro u u'
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have heps : 0 < L.sc.eps := L.sc.eps_pos
  have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow hx1.le heps.le
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (by linarith)
  have hx6 : 1 ≤ L.sc.x ^ 6 := one_le_pow₀ hx1.le
  have hM1 : 1 ≤ 6 * L.sc.x ^ 6 * L.sc.b := by
    have h6 : 1 ≤ 6 * L.sc.x ^ 6 := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ 6 * L.sc.x ^ 6 * L.sc.b := mul_le_mul h6 hb1 (by norm_num) (by linarith)
  have h := compl3_abs_le D L Z Csz (6 * L.sc.x ^ 6 * L.sc.b) hM1 (fun i hi τ => sc_add_wj_le D L S i hi τ) u u'
  refine le_trans h ?_
  have hlogM := log_M_le L.sc
  have hOm := abs_logOm_le D L S P
  have hkSc := kSc_le_b D L S
  have hQ0 : 0 ≤ Real.log (6 * L.sc.x ^ 6 * L.sc.b) + |L.logOm| :=
    add_nonneg (Real.log_nonneg hM1) (abs_nonneg _)
  have hK0 : 0 ≤ 14 + 6 / L.sc.eps := by positivity
  have hQ : Real.log (6 * L.sc.x ^ 6 * L.sc.b) + |L.logOm| ≤ (14 + 6 / L.sc.eps) * L.sc.L := by
    have e1 : 6 * (L.sc.L / L.sc.eps) = 6 / L.sc.eps * L.sc.L := by ring
    have e2 : (14 + 6 / L.sc.eps) * L.sc.L = 14 * L.sc.L + 6 / L.sc.eps * L.sc.L := by ring
    linarith
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hb0 : 0 ≤ L.sc.b := by linarith
  have hL0 : 0 ≤ L.sc.L := by linarith
  have h1 : (D.R.k : ℝ) * (L.Sc * (Real.log (6 * L.sc.x ^ 6 * L.sc.b) + |L.logOm|)) ≤
      L.sc.b * ((14 + 6 / L.sc.eps) * L.sc.L) := by
    rw [← mul_assoc]
    exact mul_le_mul hkSc hQ hQ0 hb0
  have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hf0) hm0
  refine le_trans h2 ?_
  have hB0 : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L := rfl
  obtain ⟨_, _, _, _, _, _, hQD, _⟩ := S
  have hrd : 1 ≤ D.host.rdE := hQD.2.2.2.2.2.2.1
  have ha1 : 1 ≤ L.sc.a := by
    unfold Scale.a
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ L.sc.x * L.sc.b := mul_le_mul hx1.le hb1 (by norm_num) (by linarith)
  have hLa0 : 0 ≤ L.La := by
    unfold SizeData₂.La
    apply Real.log_nonneg
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ L.sc.a * D.host.rdE := mul_le_mul ha1 hrd (by norm_num) (by linarith)
  have hTaLa : 0 ≤ (D.host.TT.card : ℝ) * L.sc.a * L.La :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hLa0
  have hC0 : 0 ≤ 20 + 6 / L.sc.eps := by positivity
  have hY : 0 ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L := by positivity
  calc (D.R.m : ℝ) * ((D.R.f : ℝ) * (L.sc.b * ((14 + 6 / L.sc.eps) * L.sc.L)))
      = (14 + 6 / L.sc.eps) * ((D.R.m : ℝ) * ((D.R.f : ℝ) * L.sc.b * L.sc.L)) := by ring
    _ ≤ (20 + 6 / L.sc.eps) * ((D.R.m : ℝ) * ((D.R.f : ℝ) * L.sc.b * L.sc.L)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hm0 hY)
    _ ≤ (20 + 6 / L.sc.eps) * ((D.R.m : ℝ) * ((D.R.f : ℝ) * L.sc.b * L.sc.L) * D.R.m) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (mul_nonneg hm0 hY) hm1) hC0
    _ = (20 + 6 / L.sc.eps) * ((D.R.m : ℝ) * L.B0) := by rw [hB0]; ring
    _ ≤ (20 + 6 / L.sc.eps) * ((D.host.TT.card : ℝ) * L.sc.a * L.La + (D.R.m : ℝ) * L.B0) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hTaLa) hC0

theorem rbCompl3 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) :
    ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.L2.DIV.Compl3 (Fm.L x i) (Fm.X x i) Fm.Csz C := by
  refine ⟨20 + 6 / eps, Fm.x1 + 1, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by linarith
  have h := compl3_record (Fm.D x i) (Fm.L x i) (Fm.X x i) Fm.Csz (Fm.params x hx1 i) (Fm.sizes x hx1 i)
  rwa [Fm.L_eps x i] at h

end Formalism.MainNotions.DIV.HookProducts.RBCompl3

end
