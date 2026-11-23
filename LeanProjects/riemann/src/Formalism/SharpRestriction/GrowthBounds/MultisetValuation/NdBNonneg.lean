import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NdLszLe

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem nd_x_ge : (1 : ℝ) ≤ L.sc.x := le_of_lt L.sc.one_lt_alt

theorem nd_b'_nonneg : 0 ≤ L.sc.b' := by
  have hx : (1 : ℝ) < L.sc.x := L.sc.one_lt_alt
  unfold Scale.b' Scale.a Scale.X' Scale.b
  exact div_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) (Real.exp_pos _).le

theorem nd_b'_le : L.sc.b' ≤ L.sc.a := by
  have hx : (1 : ℝ) < L.sc.x := L.sc.one_lt_alt
  have ha : 0 ≤ L.sc.a := by
    unfold Scale.a Scale.b
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  unfold Scale.b'
  apply div_le_self ha
  unfold Scale.X'
  exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)

theorem nd_n_ge : (1 : ℝ) ≤ (D.R.n : ℝ) := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_le_f
  have h3 : 1 ≤ D.R.n := by unfold Ranks.n; omega
  exact_mod_cast h3

theorem nd_w''_le : L.sc.w'' D.R.n ≤ L.sc.b' := by
  unfold Scale.w''
  exact div_le_self nd_b'_nonneg (one_le_mul_of_one_le_of_one_le nd_x_ge nd_n_ge)

theorem nd_m_ge : (2 : ℝ) ≤ (D.R.m : ℝ) := by
  exact_mod_cast D.R.two_le_m

theorem nd_k_ge : (5 : ℝ) ≤ (D.R.k : ℝ) := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have h3 : 5 ≤ D.R.k := by omega
  exact_mod_cast h3

theorem nd_eta_le (hS : Formalism.MainNotions.SizesAt L) : L.etaSz ≤ L.sc.a := by
  unfold Formalism.MainNotions.SizesAt at hS
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := hS
  unfold Formalism.MainNotions.SizeEta at hE
  have h2 := hE.2.1
  have hx : (1 : ℝ) ≤ L.sc.x := nd_x_ge
  have hb : 0 ≤ L.sc.b := by unfold Scale.b; exact (Real.exp_pos _).le
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) := by
    have := D.R.rank_add_five_le
    have h : 1 ≤ D.R.t := by omega
    exact_mod_cast h
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    have h : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; omega
    exact_mod_cast h
  have hk : (1 : ℝ) ≤ (D.R.k : ℝ) := by have := nd_k_ge (D := D); linarith
  have hd : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) hf) (one_le_pow₀ hk)
  calc L.etaSz ≤ _ := h2
    _ ≤ L.sc.b := div_le_self hb hd
    _ ≤ L.sc.a := by unfold Scale.a; exact le_mul_of_one_le_left hb hx

theorem nd_Sc_le (hS : Formalism.MainNotions.SizesAt L) : 4 * L.Sc ≤ L.sc.a := by
  have hS' := hS
  unfold Formalism.MainNotions.SizesAt at hS'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := hS'
  unfold Formalism.MainNotions.SizeEta at hE
  obtain ⟨h1, -, -, -, -, h6, -⟩ := hE
  have hx : (1 : ℝ) ≤ L.sc.x := nd_x_ge
  have hx0 : (0 : ℝ) < L.sc.x := by linarith
  have hn : (1 : ℝ) ≤ (D.R.n : ℝ) := nd_n_ge
  have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := nd_m_ge
  have hb' : 0 ≤ L.sc.b' := nd_b'_nonneg
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    exact div_nonneg hb' (mul_nonneg hx0.le (by positivity))
  have heta : 0 ≤ L.etaSz := le_trans (by positivity) h1
  have hSc : 0 < L.Sc := L.Sc_pos
  have hL : L.sc.L ≤ L.sc.x := by
    unfold Scale.L
    calc L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith [L.sc.eps_lt])
      _ = L.sc.x := Real.rpow_one _
  have hwx : L.sc.w'' D.R.n * L.sc.x ≤ L.sc.b' := by
    unfold Scale.w''
    rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos hx0 (by linarith))]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hx0.le hn) hb'
  have hX : 2 ≤ L.sc.X' := by
    unfold Scale.X'
    have h1' : (1 : ℝ) ≤ L.sc.x ^ (L.sc.eps / 3) := Real.one_le_rpow hx (by linarith [L.sc.eps_pos])
    linarith [Real.add_one_le_exp (L.sc.x ^ (L.sc.eps / 3))]
  have ha : 0 ≤ L.sc.a := by
    unfold Scale.a Scale.b
    exact mul_nonneg hx0.le (Real.exp_pos _).le
  have hb'a : 2 * L.sc.b' ≤ L.sc.a := by
    unfold Scale.b'
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hX ha]
  linarith [mul_le_mul_of_nonneg_left hL hw0, mul_le_mul_of_nonneg_right hm (add_nonneg hSc.le heta)]

theorem nd_bT_le (hS : Formalism.MainNotions.SizesAt L) (t : D.host.TT) : (L.bT t : ℝ) ≤ 5 / 4 * L.sc.a := by
  have hS' := hS
  unfold Formalism.MainNotions.SizesAt at hS'
  obtain ⟨hN, -, hK, -, -, -, -, -, hLa, -, hBot, -⟩ := hS'
  unfold Formalism.MainNotions.SizeN at hN
  unfold Formalism.MainNotions.SizeK at hK
  unfold Formalism.MainNotions.SizeLa at hLa
  unfold Formalism.MainNotions.SizeBot at hBot
  have hb := hBot t
  unfold Formalism.MainNotions.szNst at hb
  unfold Formalism.MainNotions.szTh at hN hK hLa
  have hx : (1 : ℝ) ≤ L.sc.x := nd_x_ge
  have hx0 : (0 : ℝ) < L.sc.x := by linarith
  have he0 : 0 < L.sc.eps := L.sc.eps_pos
  have he1 : L.sc.eps < 1 / 52 := L.sc.eps_lt
  have hk0 : (0 : ℝ) < (D.R.k : ℝ) := by have := nd_k_ge (D := D); linarith
  have hxe0 : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hx0.le _
  have hLa0 : 0 ≤ L.LaG := le_trans hxe0 hLa.1
  have hn0 : (0 : ℝ) ≤ (D.R.n : ℝ) := by positivity
  have hkey : (D.R.n : ℝ) * L.sc.x ^ L.sc.eps * L.LaG ≤ (D.R.k : ℝ) := by
    calc (D.R.n : ℝ) * L.sc.x ^ L.sc.eps * L.LaG
        ≤ L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100) * L.sc.x ^ L.sc.eps *
            L.sc.x ^ (L.sc.eps + L.sc.eps / 100) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hN.2 hxe0) hLa.2 hLa0
            (mul_nonneg (Real.rpow_nonneg hx0.le _) hxe0)
      _ = L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100 + L.sc.eps + (L.sc.eps + L.sc.eps / 100)) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      _ ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - L.sc.eps / 100) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ ≤ (D.R.k : ℝ) := hK.1
  have hd1 : L.sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  have hd0 : 0 ≤ L.sc.delta1 := by
    unfold Scale.delta1
    exact Real.rpow_nonneg hx0.le _
  have hb' : 0 ≤ L.sc.b' := nd_b'_nonneg
  have hE : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) ≤
      2 * L.sc.b' := by
    rw [div_le_iff₀ hk0]
    nlinarith [mul_le_mul_of_nonneg_left hkey (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd0) hb'),
      mul_le_mul_of_nonneg_right hd1 (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb') hk0.le)]
  have ha : 0 ≤ L.sc.a := by
    unfold Scale.a Scale.b
    exact mul_nonneg hx0.le (Real.exp_pos _).le
  have hX : 12 / 5 ≤ L.sc.X' := by
    unfold Scale.X'
    have h1' : (1 : ℝ) ≤ L.sc.x ^ (L.sc.eps / 3) := Real.one_le_rpow hx (by linarith)
    first
    | nlinarith [Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ L.sc.x ^ (L.sc.eps / 3) by linarith)]
    | (have h2' := Real.exp_le_exp.mpr h1'; have h3' := Real.exp_one_gt_d9; linarith)
  have hb'a : 3 * L.sc.b' ≤ 5 / 4 * L.sc.a := by
    unfold Scale.b'
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hX ha]
  linarith

theorem nd_aT_le (t : D.host.TT) : (L.aT t : ℝ) ≤ 2 * L.sc.a := by
  have hw := (L.aT_win t).2
  have hx : (1 : ℝ) ≤ L.sc.x := nd_x_ge
  have ha : 0 ≤ L.sc.a := by
    unfold Scale.a Scale.b
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  have hk : (1 : ℝ) ≤ (D.R.k : ℝ) := by have := nd_k_ge (D := D); linarith
  have hp : (1 : ℝ) ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow hx (by unfold Scale.A; norm_num)
  have hd : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a :=
    div_le_self ha (one_le_mul_of_one_le_of_one_le hk hp)
  linarith

theorem nd_N_le (hS : Formalism.MainNotions.SizesAt L) : (D.R.N D.R.m : ℝ) ≤ L.sc.a := by
  have hS' := hS
  unfold Formalism.MainNotions.SizesAt at hS'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := hS'
  unfold Formalism.MainNotions.SizeEta at hE
  obtain ⟨h1, h2, -⟩ := hE
  have hx : (1 : ℝ) ≤ L.sc.x := nd_x_ge
  have hb : 0 ≤ L.sc.b := by unfold Scale.b; exact (Real.exp_pos _).le
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hmf := D.R.m_le_f
  have htr := D.R.rank_add_five_le
  have hf : 2 ≤ D.R.f := by unfold Ranks.f Ranks.n; omega
  have ht : 1 ≤ D.R.t := by omega
  have hk : 5 ≤ D.R.k := by omega
  have hNn : D.R.N D.R.m ≤ D.R.t ^ 3 * D.R.f * D.R.k ^ 3 := by
    have e1 : D.R.m * (D.R.t + 1) ≤ D.R.k * (D.R.t + 1) := Nat.mul_le_mul_right _ (by omega)
    have e2 : D.R.k * (D.R.t + 2) ≤ D.R.k * (3 * D.R.t) := Nat.mul_le_mul_left _ (by omega)
    have e3 : 3 ≤ D.R.f * D.R.k ^ 2 := by nlinarith
    have e4 : D.R.t * 3 ≤ D.R.t ^ 3 * (D.R.f * D.R.k ^ 2) :=
      Nat.mul_le_mul (Nat.le_self_pow (by norm_num) _) e3
    unfold Ranks.N
    calc D.R.k + D.R.m * (D.R.t + 1) ≤ D.R.k * (D.R.t + 2) := by nlinarith [e1]
      _ ≤ D.R.k * (3 * D.R.t) := e2
      _ = D.R.k * (D.R.t * 3) := by ring
      _ ≤ D.R.k * (D.R.t ^ 3 * (D.R.f * D.R.k ^ 2)) := Nat.mul_le_mul_left _ e4
      _ = D.R.t ^ 3 * D.R.f * D.R.k ^ 3 := by ring
  have hNr : (D.R.N D.R.m : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := by exact_mod_cast hNn
  have ht0 : (0 : ℝ) < D.R.t := by exact_mod_cast (show 0 < D.R.t by omega)
  have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast (show 0 < D.R.f by omega)
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast (show 0 < D.R.k by omega)
  have hdpos : 0 < (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 :=
    mul_pos (mul_pos (pow_pos ht0 3) hf0) (pow_pos hk0 3)
  have ht1 : (1 : ℝ) ≤ L.etaSz := le_trans (by exact_mod_cast ht) h1
  have hde : (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 * L.etaSz ≤ L.sc.b := by
    rw [le_div_iff₀ hdpos] at h2
    linarith
  calc (D.R.N D.R.m : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := hNr
    _ ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 * L.etaSz := le_mul_of_one_le_right hdpos.le ht1
    _ ≤ L.sc.b := hde
    _ ≤ L.sc.a := by unfold Scale.a; exact le_mul_of_one_le_left hb hx

theorem nd_fill_le (X : Formalism.MainNotions.G.Inst D L) (hS : Formalism.MainNotions.SizesAt L) (j : ℕ) (hj : 1 ≤ j) (t : Formalism.MainNotions.G.HH D) :
    Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) j (false, t) ≤ 4 * L.sc.a := by
  have hx : (1 : ℝ) ≤ L.sc.x := nd_x_ge
  have hb'a : L.sc.b' ≤ L.sc.a := nd_b'_le
  have hb'0 : 0 ≤ L.sc.b' := nd_b'_nonneg
  have heta : L.etaSz ≤ L.sc.a := nd_eta_le hS
  have hw : L.sc.w'' D.R.n ≤ L.sc.b' := nd_w''_le
  have hka : 0 ≤ Formalism.MainNotions.G.kaJ D j := by
    unfold Formalism.MainNotions.G.kaJ
    have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have h2 : (0 : ℝ) ≤ (D.R.t : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ (D.R.k : ℝ) := by positivity
    apply div_nonneg _ (by norm_num)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (j : ℝ) - 1) (by linarith : (0 : ℝ) ≤ (D.R.t : ℝ) + 1)]
  unfold Formalism.MainNotions.G.fillG Formalism.MainNotions.G.fill
  dsimp only
  split_ifs with hc
  · have ht : t ∈ D.host.TT := hc.2
    have htop : Formalism.MainNotions.G.IsTopPl D (false, t) := by
      unfold Formalism.MainNotions.G.IsTopPl
      exact ⟨rfl, ht⟩
    have ho := (X.off_top j (false, t) htop).2
    have hbl : ((Formalism.MainNotions.G.bL L t : ℤ) : ℝ) ≤ 5 / 4 * L.sc.a := by
      unfold Formalism.MainNotions.G.bL
      rw [dif_pos ht]
      exact nd_bT_le hS ⟨t, ht⟩
    have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0 hx
    linarith
  · have hthin : Formalism.MainNotions.G.IsThinPl D (false, t) := by
      unfold Formalism.MainNotions.G.IsThinPl Formalism.MainNotions.G.IsTopPl Formalism.MainNotions.G.IsThickPl
      dsimp only
      exact ⟨fun h => hc ⟨rfl, h.2⟩, fun h => Bool.false_ne_true h.1⟩
    have ho := (X.off_thin j (false, t) hthin).2
    linarith

theorem nd_size : nd_NeedSize := by
  intro D L X Y hS hT hL u w hg _ t0 ht0 j hj
  have hm := nc_m_ge hT u w hg
  obtain ⟨_, ht, hc, _, _, _, hloc⟩ := hL u w hg
  obtain ⟨_, hs⟩ := hloc t0 ht0
  have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
  have hjm : j ≤ D.R.m := (Finset.mem_Icc.1 hj).2
  have ha := nc_a_ge (L := L)
  have hc' : ((Y.Fl u w hg).c : ℝ) ≤ L.sc.a := le_trans hc (by unfold Formalism.MainNotions.G.cG; exact nd_Sc_le hS)
  refine ⟨fun s => ?_, fun s => ?_⟩
  · by_cases hsT : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)
    · obtain ⟨_, hTT, hab, _⟩ := hs s
      have h1 := nd_al_le (Y.Fl u w hg) (Y.vOf u w hg t0) s hsT hm
      have h2 := (hab hsT).1
      have h3 : (al ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) s : ℝ) ≤
          (((Y.Fl u w hg).a (Y.vOf u w hg t0) s + ((Y.Fl u w hg).c : ℤ) : ℤ) : ℝ) := by exact_mod_cast h1
      rw [h2] at h3
      push_cast at h3
      have h4 : (Formalism.MainNotions.G.aL L (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) : ℝ) ≤ 2 * L.sc.a := by
        unfold Formalism.MainNotions.G.aL
        rw [dif_pos (hTT.1 hsT)]
        exact nd_aT_le _
      nlinarith
    · unfold al
      rw [if_neg hsT]
      push_cast
      positivity
  · obtain ⟨_, _, _, hw⟩ := hs s
    have h1 := nd_lsz_le (Y.Fl u w hg) (Y.vOf u w hg t0) s hm j hj1
    have h2 : (lsz (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
        ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j s : ℝ) ≤
        (((NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℤ) *
          (((Y.Fl u w hg).c : ℤ) + (Y.Fl u w hg).w (Y.vOf u w hg t0) j s) : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    have hk := hT.gat_k u w hg
    have hN1 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      unfold NN Ranks.N
      rw [ht]
      have : (D.gat u w hg).P.m + 1 + j * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + 1) := by
        rw [hk]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hjm) _
      exact_mod_cast this
    have hN := le_trans hN1 (nd_N_le hS)
    have hw1 : ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤ 4 * L.sc.a := by
      rw [hw j hj]; exact nd_fill_le X hS j hj1 _
    have hw0 : (0 : ℝ) ≤ ((Y.Fl u w hg).c : ℝ) + ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) := by
      have h5 := nd_c_le_w (Y.Fl u w hg) (Y.vOf u w hg t0) s j hj1
      have h6 : (((Y.Fl u w hg).c : ℤ) : ℝ) ≤ ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) := by exact_mod_cast h5
      have h7 : (0 : ℝ) ≤ ((Y.Fl u w hg).c : ℝ) := Nat.cast_nonneg _
      push_cast at h6
      linarith
    have h8 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℝ) *
        (((Y.Fl u w hg).c : ℝ) + ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ)) ≤ L.sc.a * (5 * L.sc.a) :=
      mul_le_mul hN (by linarith) hw0 (by linarith)
    have h9 : L.sc.a * (5 * L.sc.a) ≤ (2 * L.sc.a) ^ 4 := by
      have : 1 ≤ L.sc.a ^ 2 := by nlinarith
      nlinarith [sq_nonneg (L.sc.a ^ 2)]
    linarith

end Formalism.MainNotions.FormalGroupSystem.Pf
