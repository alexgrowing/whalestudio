import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeOfExplicitAndCompact
import Formalism.SharpRestriction.GlobalSchurBounds.JointsL

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions

namespace JDB

section

open Formalism.FrobeniusOrbits

theorem ra_cond {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx : 3 ≤ L.sc.x) :
    2 * D.host.v ≤ L.sc.b ∧ 2 * (D.R.k : ℝ) ≤ L.sc.b := by

  have hx0 : 0 < L.sc.x := by linarith
  have hQD := S.2.2.2.2.2.2.1
  have hT := S.2.2.2.2.1
  have h5 := S.2.2.2.2.2.1
  simp only [SizeCond, szCond] at h5
  simp only [SizeQD] at hQD
  obtain ⟨hq1, -, -, hd1, -, -, hr1, hr2⟩ := hQD
  have hq : (1 : ℝ) ≤ D.host.q := by
    by_contra hc
    push_neg at hc
    have h6 : Real.log (D.host.q : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) hc.le
    have h7 : 0 < L.sc.x ^ (L.sc.ez / 6) := Real.rpow_pos_of_pos hx0 _
    linarith
  have hd : (1 : ℝ) ≤ D.host.d := by
    by_contra hc
    push_neg at hc
    have h6 : Real.log (D.host.d : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) hc.le
    have h7 : 0 < L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) := Real.rpow_pos_of_pos hx0 _
    linarith
  have hQS : (1 : ℝ) ≤ D.host.QS := by
    rcases Nat.eq_zero_or_pos D.host.QS with h0 | h0
    · rw [h0] at hr2
      norm_num at hr2
      linarith
    · exact_mod_cast h0
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hsq : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ (D.host.q : ℝ) * D.host.d),
      Real.sqrt_nonneg ((D.host.q : ℝ) * D.host.d),
      sq_nonneg (Real.sqrt ((D.host.q : ℝ) * D.host.d) - 1)]
  have hc1 : (1 : ℝ) ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by nlinarith
  have hc36 : (D.host.QS : ℝ) * D.host.q * D.host.d ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 :=
    le_self_pow₀ hc1 (by norm_num)
  have hL : 0 < L.sc.L := by
    show 0 < L.sc.x ^ L.sc.eps
    exact Real.rpow_pos_of_pos hx0 _
  have hb : 1 ≤ L.sc.b := by
    have h8 := Real.add_one_le_exp L.sc.L
    simp only [Formalism.BasicNotions.Scale.b]
    linarith
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := by
    nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ L.sc.b), Real.sqrt_nonneg L.sc.b,
      sq_nonneg (Real.sqrt L.sc.b - 1)]
  have htk : (D.R.k : ℝ) + 6 ≤ D.R.t := by
    have h9 := D.R.rank_add_five_le
    have h10 := D.R.two_le_m
    exact_mod_cast (by omega : D.R.k + 6 ≤ D.R.t)
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    linarith
  have ht2 : (D.R.t : ℝ) ^ 2 ≤ (D.R.t : ℝ) ^ 150 := pow_le_pow_right₀ ht1 (by norm_num)
  have ht150 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht1
  have hc36' : (1 : ℝ) ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 := le_trans hc1 hc36
  have hv : 2 * D.host.v = D.host.rdE := by
    simp only [Formalism.BasicNotions.Host.v]
    ring
  constructor
  · rw [hv]
    have h11 : D.host.rdE ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by
      have h12 : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d)
          ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by
        have : (0 : ℝ) ≤ D.host.QS := Nat.cast_nonneg _
        nlinarith [Real.sqrt_nonneg ((D.host.q : ℝ) * D.host.d)]
      nlinarith
    nlinarith
  · have h13 : 2 * (D.R.k : ℝ) ≤ (D.R.t : ℝ) ^ 2 := by nlinarith
    nlinarith

theorem rank_m_le_x {D : D7} (L : SizeData₂ D) (S : SizesAt L) : (D.R.m : ℝ) ≤ L.sc.x := by

  have hx1 : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hx0 : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have he := L.sc.eps_pos
  have he2 := L.sc.eps_lt
  have h1 := S.2.1
  simp only [SizeM, szTh] at h1
  have hd : L.sc.delta1 ≤ 1 := by
    simp only [Formalism.BasicNotions.Scale.delta1]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hs : Real.sqrt (L.sc.x * L.sc.delta1) ≤ Real.sqrt L.sc.x :=
    Real.sqrt_le_sqrt (mul_le_of_le_one_right hx0.le hd)
  have hp : L.sc.x ^ (L.sc.eps / 100) ≤ Real.sqrt L.sc.x := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsn := Real.sqrt_nonneg (L.sc.x * L.sc.delta1)
  calc (D.R.m : ℝ) ≤ L.sc.x ^ (L.sc.eps / 100) * Real.sqrt (L.sc.x * L.sc.delta1) := h1.2
    _ ≤ Real.sqrt L.sc.x * Real.sqrt L.sc.x := mul_le_mul hp hs hsn (Real.sqrt_nonneg _)
    _ = L.sc.x := Real.mul_self_sqrt hx0.le

theorem ra_44 {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx : (44 : ℝ) ^ 4 ≤ L.sc.x) : 44 ≤ D.R.m := by

  have hx1 : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hx0 : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have he := L.sc.eps_pos
  have he2 := L.sc.eps_lt
  have h1 := S.2.1
  simp only [SizeM, szTh] at h1
  have hkey : L.sc.x ^ (-(L.sc.eps / 100)) * Real.sqrt (L.sc.x * L.sc.delta1)
      = L.sc.x ^ (-(L.sc.eps / 100) + (1 + -(L.sc.eps / 8)) * (1 / 2)) := by
    simp only [Formalism.BasicNotions.Scale.delta1]
    rw [Real.sqrt_eq_rpow, show L.sc.x * L.sc.x ^ (-(L.sc.eps / 8)) = L.sc.x ^ (1 + -(L.sc.eps / 8)) by
      rw [Real.rpow_add hx0, Real.rpow_one], ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
  have hge : L.sc.x ^ ((1 : ℝ) / 4) ≤ L.sc.x ^ (-(L.sc.eps / 100) + (1 + -(L.sc.eps / 8)) * (1 / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h44 : (44 : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 4) := by
    have h2 := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 44 ^ 4) hx (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 44)] at h2
    norm_num at h2 ⊢
    linarith
  have h3 : (44 : ℝ) ≤ D.R.m := by linarith [h1.1]
  exact_mod_cast h3

theorem ra_Sc {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (S : SizesAt L) (hx : (44 : ℝ) ^ 4 ≤ L.sc.x) :
    0 ≤ L.Sc ∧ L.Sc ≤ L.sc.b' ∧ L.sc.b' ≤ L.sc.b ∧ 100 * L.sc.b ≤ L.sc.a := by

  have hx1 : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hx0 : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have he := L.sc.eps_pos
  have he2 := L.sc.eps_lt
  have hx100 : (100 : ℝ) ≤ L.sc.x := by norm_num at hx; linarith
  have hb0 : 0 < L.sc.b := by simp only [Formalism.BasicNotions.Scale.b]; exact Real.exp_pos _
  have hb'0 : 0 ≤ L.sc.b' := by
    simp only [Formalism.BasicNotions.Scale.b', Formalism.BasicNotions.Scale.a, Formalism.BasicNotions.Scale.X']
    positivity
  have h1 := S.2.1
  simp only [SizeM, szTh] at h1
  have hDel := S.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [SizeDel, szTh] at hDel
  obtain ⟨hD1, -, hD3, hD4, -⟩ := hDel
  have hk5 : (5 : ℝ) ≤ D.R.k := by
    have h2 := D.R.m_add_three_le_k
    have h3 := D.R.two_le_m
    exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have h4 : 1 ≤ D.R.n := by
      show 1 ≤ D.R.ord
      have h2 := D.R.two_le_m
      have h3 := D.R.m_le_f
      omega
    exact_mod_cast h4
  have hScp := L.Sc_pos
  have hw'' : L.sc.w'' D.R.n ≤ L.sc.b' := by
    simp only [Formalism.BasicNotions.Scale.w'']
    exact div_le_self hb'0 (by nlinarith)

  have hkey : L.sc.x ^ (-(L.sc.eps / 100)) * Real.sqrt (L.sc.x * L.sc.delta1)
      = L.sc.x ^ (-(L.sc.eps / 100) + (1 + -(L.sc.eps / 8)) * (1 / 2)) := by
    simp only [Formalism.BasicNotions.Scale.delta1]
    rw [Real.sqrt_eq_rpow, show L.sc.x * L.sc.x ^ (-(L.sc.eps / 8)) = L.sc.x ^ (1 + -(L.sc.eps / 8)) by
      rw [Real.rpow_add hx0, Real.rpow_one], ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
  have hge : L.sc.x ^ ((1 : ℝ) / 4) ≤ L.sc.x ^ (-(L.sc.eps / 100) + (1 + -(L.sc.eps / 8)) * (1 / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hm4 : L.sc.x ^ ((1 : ℝ) / 4) ≤ (D.R.m : ℝ) := by linarith [h1.1]
  have hq0 : 0 < L.sc.x ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hx0 _
  have hm0 : (0 : ℝ) < D.R.m := lt_of_lt_of_le hq0 hm4
  have hN1 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have h5 : 1 ≤ D.R.N D.R.m := by
      simp only [Formalism.BasicNotions.Ranks.N]
      have h2 := D.R.m_add_three_le_k
      omega
    exact_mod_cast h5
  have hm10 : (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ) := by
    have h6 : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := by positivity
    nlinarith
  have hlogm : Real.log ((D.R.m : ℝ) ^ 10) ≤ Real.log (D.s.Del : ℝ) :=
    Real.log_le_log (by positivity) hm10
  rw [Real.log_pow] at hlogm
  have hlm : 1 / 4 * Real.log L.sc.x ≤ Real.log (D.R.m : ℝ) := by
    have h7 := Real.log_le_log hq0 hm4
    rwa [Real.log_rpow hx0] at h7
  have hex : L.sc.x ^ (L.sc.eps / 4) ≤ L.sc.x ^ (L.sc.eps / 3) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hlx : Real.log L.sc.x ≤ L.sc.x ^ (L.sc.eps / 3) := by
    push_cast at hlogm
    nlinarith [Real.log_nonneg hx1]
  have hxe : L.sc.x ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3)) := by
    calc L.sc.x = Real.exp (Real.log L.sc.x) := (Real.exp_log hx0).symm
      _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3)) := Real.exp_le_exp.mpr hlx
  refine ⟨hScp.le, ?_, ?_, ?_⟩
  · nlinarith
  · simp only [Formalism.BasicNotions.Scale.b', Formalism.BasicNotions.Scale.a, Formalism.BasicNotions.Scale.X']
    rw [div_le_iff₀ (Real.exp_pos _)]
    nlinarith [mul_le_mul_of_nonneg_right hxe hb0.le]
  · simp only [Formalism.BasicNotions.Scale.a]
    nlinarith [mul_le_mul_of_nonneg_right hx100 hb0.le]

theorem rowsA_of' {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (S : SizesAt L) (hx : (44 : ℝ) ^ 4 ≤ L.sc.x) (CY : ℝ)
    (hg : ∀ i : Fin 2, Real.log (D.host.g i : ℝ) ≤ CY * L.sc.L) :
    StandardLattice.RowsA D L.sc CY ((D.s.Del : ℚ) : ℝ) := by
  have hx3 : 3 ≤ L.sc.x := le_trans (by norm_num) hx
  obtain ⟨hk3, hm2, hkt, hkr, hn1, hf, hmk⟩ := db_rk D
  obtain ⟨hL1, hLx, hb2, hkb, hvb, hlx⟩ := db_basic L S hx3
  obtain ⟨h2v, h2k⟩ := ra_cond L S hx3
  obtain ⟨hS0, hSb', hb'b, ha100⟩ := ra_Sc L P S hx
  obtain ⟨c8, c9, c10, c12⟩ := db_cloud L P
  have hpiv := db_pi_le_v D
  have hkN := D.R.m_add_three_le_k
  have hk0 : 0 < D.R.k := by omega
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hbexp : L.sc.b = Real.exp L.sc.L := rfl
  have hSc := L.Sc_eq

  have top : ∀ (u : D.what₂.Word) ρ, StandardLattice.IsTop D ρ → ∃ t : D.host.TT,
      StandardLattice.uN D u ρ 0 = L.aT t + ((D.R.k : ℝ) - 1) / 2 ∧
      StandardLattice.uN D u ρ (D.R.k - 1) = -(L.bT t : ℝ) - ((D.R.k : ℝ) - 1) / 2 := by
    intro u ρ htop
    have htop' : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces := htop
    unfold Host.topPlaces at htop'
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp htop'
    obtain ⟨a1, a2⟩ := L.top_u ρ ⟨t, ht⟩ hk0 heq.symm
    refine ⟨⟨t, ht⟩, ?_, ?_⟩
    · rw [db_uN u ρ 0 hk0, D.hcW_first u ρ hk0, a1]
    · rw [db_uN u ρ (D.R.k - 1) (by omega), D.hcW_last u ρ hk0, a2]
  refine ⟨?_, hg, ra_44 L S hx, by omega, rank_m_le_x L S, ?_, ?_, ?_⟩
  · have h1 := Real.log_le_log (by linarith [Real.pi_pos]) h2v
    rwa [hbexp, Real.log_exp] at h1
  · have h1 := Real.log_le_log (by linarith) h2k
    rwa [hbexp, Real.log_exp] at h1
  · intro u ρ
    by_cases htop : StandardLattice.IsTop D ρ
    · obtain ⟨t, e1, e2⟩ := top u ρ htop
      rw [e1, e2]
      obtain ⟨w1, w2⟩ := L.aT_win t
      have ha0 : 0 < L.sc.a := by linarith
      have hxa : 1 ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow hx1 (by unfold Scale.A; norm_num)
      have hden : 3 ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) := by nlinarith
      have h3 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 3 :=
        div_le_div_of_nonneg_left ha0.le (by norm_num) hden
      have hbT := db_bT L S hx3 t
      linarith
    · obtain ⟨d1, d2, d3⟩ := c12 u ρ htop
      have v0 := (c8 ρ 0 (by omega)).2
      have vk := (c8 ρ (D.R.k - 2) (by omega)).1
      rw [d3]
      rw [← hSc] at v0
      have d2' : StandardLattice.uN D u ρ 0 - StandardLattice.vN D ρ 0 ≤ 2 * L.Sc := by rw [hSc]; linarith
      linarith
  · intro u ρ htop
    obtain ⟨t, e1, e2⟩ := top u ρ htop
    rw [e1, e2, ← hSc]
    obtain ⟨w1, w2⟩ := L.aT_win t
    have hb := L.bT_ge t
    have v0 := (c8 ρ 0 (by omega)).2
    rw [← hSc] at v0
    constructor <;> linarith

theorem rowsA_of {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (S : SizesAt L) (hx : (44 : ℝ) ^ 4 ≤ L.sc.x) :
    StandardLattice.RowsA D L.sc (max 5 (P.CYL + 1)) ((D.s.Del : ℚ) : ℝ) := by
  have hx3 : (3 : ℝ) ≤ L.sc.x := by norm_num at hx; linarith
  obtain ⟨Y, hY1, -, hY3, hY4⟩ := P.g_Y
  have hx0 : 0 < L.sc.x := by linarith
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hL : 0 < L.sc.L := by
    show 0 < L.sc.x ^ L.sc.eps
    exact Real.rpow_pos_of_pos hx0 _
  have hL1 : 1 ≤ L.sc.L := by
    show 1 ≤ L.sc.x ^ L.sc.eps
    exact Real.one_le_rpow hx1 L.sc.eps_pos.le
  have hb : 1 ≤ L.sc.b := by
    have h8 := Real.add_one_le_exp L.sc.L
    simp only [Formalism.BasicNotions.Scale.b]
    linarith
  have hk : (1 : ℝ) ≤ D.R.k := by
    have h2 := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hY0 : 0 < Y := by
    have h9 : (1 : ℝ) ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := one_le_pow₀ (by nlinarith)
    linarith
  have hl2 := Real.log_two_lt_d9
  have hg : ∀ i : Fin 2, Real.log (D.host.g i : ℝ) ≤ max 5 (P.CYL + 1) * L.sc.L := by
    intro i
    obtain ⟨hg1, hg2⟩ := hY4 i
    have hg0 : (0 : ℝ) < D.host.g i := by linarith
    have h1 : Real.log (D.host.g i : ℝ) ≤ Real.log (2 * Y) := Real.log_le_log hg0 hg2
    rw [Real.log_mul (by norm_num) hY0.ne'] at h1
    have h2 : (P.CYL + 1) * L.sc.L ≤ max 5 (P.CYL + 1) * L.sc.L :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hL.le
    nlinarith
  exact rowsA_of' L P S hx (max 5 (P.CYL + 1)) hg

theorem dataA_of {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (S : SizesAt L) (hx : (44 : ℝ) ^ 4 ≤ L.sc.x) :
    StandardLattice.DataA D L.sc (max 5 (P.CYL + 1)) (max 5 (P.CYL + 1)) ((D.s.Del : ℚ) : ℝ) (fun j ρ => wj D (j + 1) ρ) :=
  ⟨dataB_of L P S (le_trans (by norm_num) hx), rowsA_of L P S hx⟩

theorem dataA_fam {eps : ℝ} (Fm : FamP eps) (x : ℝ) (h3 : (44 : ℝ) ^ 4 ≤ x) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    StandardLattice.DataA (Fm.D x i) (Fm.L x i).sc (max 5 (Fm.CYL + 1)) (max 5 (Fm.CYL + 1)) (((Fm.D x i).s.Del : ℚ) : ℝ)
      (fun j ρ => wj (Fm.D x i) (j + 1) ρ) := by

  have hLx := Fm.L_x x i hx
  have h3' : (44 : ℝ) ^ 4 ≤ (Fm.L x i).sc.x := by rw [hLx]; exact h3
  have hC : (Fm.params x hx i).CYL = Fm.CYL := by
    simp only [Formalism.MainNotions.FamP.CYL]
    rw [← Fm.params_K x hx i]
    rfl
  have h4 := dataA_of (Fm.L x i) (Fm.params x hx i) (Fm.sizes x hx i) h3'
  rw [hC] at h4
  exact h4

theorem rowsA_of_dataB {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (S : SizesAt L) (hx : (44 : ℝ) ^ 4 ≤ L.sc.x)
    (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : StandardLattice.DataB D L.sc C0 Δ w) : StandardLattice.RowsA D L.sc C0 Δ := by
  obtain ⟨-, -, -, -, -, h6, -, -, h9, -⟩ := hB
  obtain ⟨c8, c9, c10, c12⟩ := db_cloud L P
  have hk := D.R.k_ge
  obtain ⟨ρ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have e1 := h9 ρ 0 (by omega)
  have e2 := c9 ρ 0 (by omega)
  have hΔ : Δ = ((D.s.Del : ℚ) : ℝ) := by linarith
  rw [hΔ]
  exact rowsA_of' L P S hx C0 fun i => (h6 i).2

theorem rowsA_of_dataB_fam {eps : ℝ} (Fm : FamP eps) (x : ℝ) (h3 : (44 : ℝ) ^ 4 ≤ x) (hx : Fm.x1 < x) (i : Fm.Ix x)
    (C0 Δ : ℝ) (w : ℕ → (Fm.D x i).what₂.Tau → ℝ) (hB : StandardLattice.DataB (Fm.D x i) (Fm.L x i).sc C0 Δ w) :
    StandardLattice.RowsA (Fm.D x i) (Fm.L x i).sc C0 Δ := by
  have hLx := Fm.L_x x i hx
  have h3' : (44 : ℝ) ^ 4 ≤ (Fm.L x i).sc.x := by rw [hLx]; exact h3
  exact rowsA_of_dataB (Fm.L x i) (Fm.params x hx i) (Fm.sizes x hx i) h3' C0 Δ w hB

theorem ra_logg {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (S : SizesAt L) (hx : 3 ≤ L.sc.x) (i : Fin 2) :
    Real.log (D.host.g i : ℝ) ≤ (P.CYL + 1) * L.sc.L := by

  obtain ⟨Y, hY1, -, hY3, hY4⟩ := P.g_Y
  have hx0 : 0 < L.sc.x := by linarith
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hL : 0 < L.sc.L := by
    show 0 < L.sc.x ^ L.sc.eps
    exact Real.rpow_pos_of_pos hx0 _
  have hL1 : 1 ≤ L.sc.L := by
    show 1 ≤ L.sc.x ^ L.sc.eps
    exact Real.one_le_rpow hx1 L.sc.eps_pos.le
  have hb : 1 ≤ L.sc.b := by
    have h8 := Real.add_one_le_exp L.sc.L
    simp only [Formalism.BasicNotions.Scale.b]
    linarith
  have hk : (1 : ℝ) ≤ D.R.k := by
    have h2 := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hY0 : 0 < Y := by
    have h9 : (1 : ℝ) ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := one_le_pow₀ (by nlinarith)
    linarith
  have hl2 := Real.log_two_lt_d9
  obtain ⟨hg1, hg2⟩ := hY4 i
  have hg0 : (0 : ℝ) < D.host.g i := by linarith
  have h1 : Real.log (D.host.g i : ℝ) ≤ Real.log (2 * Y) := Real.log_le_log hg0 hg2
  rw [Real.log_mul (by norm_num) hY0.ne'] at h1
  nlinarith

theorem dataA_fam' {eps : ℝ} (Fm : FamP eps) (x : ℝ) (h3 : (44 : ℝ) ^ 4 ≤ x) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    StandardLattice.DataA (Fm.D x i) (Fm.L x i).sc (max 5 (Fm.CYL + 1)) (Fm.CYL + 1) (((Fm.D x i).s.Del : ℚ) : ℝ)
      (fun j ρ => wj (Fm.D x i) (j + 1) ρ) := by

  have hLx := Fm.L_x x i hx
  have h3' : (44 : ℝ) ^ 4 ≤ (Fm.L x i).sc.x := by rw [hLx]; exact h3
  have hC : (Fm.params x hx i).CYL = Fm.CYL := by
    simp only [Formalism.MainNotions.FamP.CYL]
    rw [← Fm.params_K x hx i]
    rfl
  have hx3 : (3 : ℝ) ≤ (Fm.L x i).sc.x := by norm_num at h3'; linarith
  refine ⟨(dataA_fam Fm x h3 hx i).1, ?_⟩
  exact rowsA_of' (Fm.L x i) (Fm.params x hx i) (Fm.sizes x hx i) h3' (Fm.CYL + 1)
    (fun j => by rw [← hC]; exact ra_logg (Fm.L x i) (Fm.params x hx i) (Fm.sizes x hx i) hx3 j)

theorem ra_w_eq {D : D7} (L : SizeData₂ D) :
    Real.log (L.sc.w'' D.R.n) = L.sc.L - L.sc.x ^ (L.sc.eps / 3) - Real.log (D.R.n : ℝ) := by

  have hn : 0 < D.R.n := by
    show 0 < D.R.ord
    have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    omega
  have hnR : (0 : ℝ) < (D.R.n : ℝ) := by exact_mod_cast hn
  have hx : (0 : ℝ) < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hw : L.sc.w'' D.R.n = Real.exp (L.sc.L - L.sc.x ^ (L.sc.eps / 3)) / (D.R.n : ℝ) := by
    simp only [Formalism.BasicNotions.Scale.w'', Formalism.BasicNotions.Scale.b', Formalism.BasicNotions.Scale.a, Formalism.BasicNotions.Scale.X',
      Formalism.BasicNotions.Scale.b]
    rw [Real.exp_sub]
    field_simp
  rw [hw, Real.log_div (Real.exp_pos _).ne' hnR.ne', Real.log_exp]

theorem ra_logw {D : D7} (L : SizeData₂ D) (S : SizesAt L)
    (hy : 4 * (1 + 9 / L.sc.eps) ≤ L.sc.x ^ (L.sc.eps / 3)) :
    3 / 4 * L.sc.L ≤ Real.log (L.sc.w'' D.R.n) := by

  have hx1 : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hx0 : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have he := L.sc.eps_pos
  have he2 := L.sc.eps_lt
  have hw := ra_w_eq L
  have hN := S.1
  simp only [SizeN, szTh] at hN
  have hn0 : (0 : ℝ) < D.R.n := by
    have h1 : 0 < D.R.n := by
      show 0 < D.R.ord
      have h2 := D.R.two_le_m
      have h3 := D.R.m_le_f
      omega
    exact_mod_cast h1
  have hlogn : Real.log (D.R.n : ℝ) ≤ (2 + 8 * L.sc.eps + L.sc.eps / 100) * Real.log L.sc.x := by
    have h4 := Real.log_le_log hn0 hN.2
    rwa [Real.log_rpow hx0] at h4
  have hlx : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx1
  obtain ⟨y, hyd⟩ : ∃ y, y = L.sc.x ^ (L.sc.eps / 3) := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hyd]; exact Real.rpow_pos_of_pos hx0 _
  have hly : Real.log y = L.sc.eps / 3 * Real.log L.sc.x := by rw [hyd, Real.log_rpow hx0]
  have hly2 : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy0
  have hL3 : L.sc.L = y ^ 3 := by
    rw [hyd, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    show L.sc.x ^ L.sc.eps = _
    congr 1
    push_cast
    ring
  rw [← hyd] at hy hw
  have hey : 4 * L.sc.eps + 36 ≤ L.sc.eps * y := by
    have h5 : 4 * (1 + 9 / L.sc.eps) * L.sc.eps = 4 * L.sc.eps + 36 := by
      field_simp
      ring
    nlinarith
  have hy4 : 4 ≤ y := by
    have : 0 ≤ 9 / L.sc.eps := by positivity
    linarith
  have hel : L.sc.eps * Real.log L.sc.x ≤ 3 * y := by nlinarith
  have hen : L.sc.eps * Real.log (D.R.n : ℝ) ≤ 7 * y := by
    have h6 : L.sc.eps * Real.log (D.R.n : ℝ)
        ≤ (2 + 8 * L.sc.eps + L.sc.eps / 100) * (L.sc.eps * Real.log L.sc.x) := by
      nlinarith [mul_le_mul_of_nonneg_left hlogn he.le]
    have h7 : (2 + 8 * L.sc.eps + L.sc.eps / 100) * (L.sc.eps * Real.log L.sc.x)
        ≤ (2 + 8 * L.sc.eps + L.sc.eps / 100) * (3 * y) :=
      mul_le_mul_of_nonneg_left hel (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right (show 2 + 8 * L.sc.eps + L.sc.eps / 100 ≤ (7 : ℝ) / 3 by linarith) hy0.le]
  have h8 : 36 * y ^ 2 ≤ L.sc.eps * y * y ^ 2 := by nlinarith [sq_nonneg y]
  have hgoal : L.sc.eps * (Real.log (D.R.n : ℝ) + y) ≤ L.sc.eps * (y ^ 3 / 4) := by
    nlinarith [mul_le_mul_of_nonneg_right he2.le hy0.le, mul_le_mul_of_nonneg_right hy4 hy0.le]
  have h9 : Real.log (D.R.n : ℝ) + y ≤ y ^ 3 / 4 := le_of_mul_le_mul_left hgoal he
  rw [hw, hL3]
  nlinarith

theorem wpp_fam {eps : ℝ} (Fm : FamP eps) : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x,
    0 < (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧
    (∀ ρ j, j < (Fm.D x i).R.m → (Fm.L x i).sc.w'' (Fm.D x i).R.n ≤ wj (Fm.D x i) (j + 1) ρ) ∧
    3 / 4 * (Fm.L x i).sc.L ≤ Real.log ((Fm.L x i).sc.w'' (Fm.D x i).R.n) := by
  have heps : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]; exact (Fm.L 0 i).sc.eps_pos
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < eps / 3)).eventually_ge_atTop (4 * (1 + 9 / eps)))
  refine ⟨max x0 3, fun x hx hx1 i => ?_⟩
  have h3 : 3 ≤ (Fm.L x i).sc.x := by rw [Fm.L_x x i hx1]; exact le_trans (le_max_right _ _) hx
  refine ⟨(db_w (Fm.L x i)).1, fun ρ j hj => (db_win (Fm.L x i) (Fm.sizes x hx1 i) h3 ρ j hj).1, ?_⟩
  apply ra_logw (Fm.L x i) (Fm.sizes x hx1 i)
  rw [Fm.L_eps x i, Fm.L_x x i hx1]
  exact hx0 x (le_trans (le_max_left _ _) hx)

end

end JDB

end Formalism.MainNotions.GlobalTheoryTheory

namespace Formalism.MainNotions.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions

theorem rowsAF_fam {eps : ℝ} (Fm : FamP eps) : StandardLattice.RowsAF Fm :=
    fun C0 => ⟨(44 : ℝ) ^ 4, fun x h3 hx i Δ w hB => JDB.rowsA_of_dataB_fam Fm x h3 hx i C0 Δ w hB⟩

theorem family_part_five_of_explicit_constants {eps : ℝ} (Fm : FamP eps) (h : StandardLattice.FamilyVandermondeCountExplicit Fm) : StandardLattice.PartFiveFamilyBounds Fm :=
    StandardLattice.part_five_family_of_explicit Fm h (rowsAF_fam Fm)

theorem _root_.Formalism.MainNotions.ShortIntervalPrimes.log_X_lower_of_corollary_five_six {eps : ℝ} (Fm : FamP eps) (h : StandardLattice.FamilyVandermondeCountExplicit Fm) : ShortIntervalPrimes.proportionalityInputFamily Fm := by
  have hB : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x,
      ∃ (Δ : ℝ) (w : ℕ → (Fm.D x i).what₂.Tau → ℝ),
        StandardLattice.DataB (Fm.D x i) (Fm.L x i).sc (max 5 (Fm.CYL + 1)) Δ w :=
    ⟨(44 : ℝ) ^ 4, fun x h3 hx i => ⟨_, _, (JDB.dataA_fam Fm x h3 hx i).1⟩⟩
  refine ShortIntervalPrimes.log_height_family_of_data Fm (max 5 (Fm.CYL + 1)) (family_part_five_of_explicit_constants Fm h) hB ?_
  intro K
  refine ⟨max ((44 : ℝ) ^ 4) ((max K 44) ^ 4), fun x hxK hx1 i => ?_⟩
  have hK' : (0 : ℝ) ≤ max K 44 := le_trans (by norm_num) (le_max_right _ _)
  have S := Fm.sizes x hx1 i
  have hxx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hx : (max K 44) ^ 4 ≤ (Fm.L x i).sc.x := by rw [hxx]; exact le_trans (le_max_right _ _) hxK
  have hx1' : 1 ≤ (Fm.L x i).sc.x := (Fm.L x i).sc.one_lt_alt.le
  have hx0 : 0 < (Fm.L x i).sc.x := by linarith [(Fm.L x i).sc.one_lt_alt]
  have he := (Fm.L x i).sc.eps_pos
  have he2 := (Fm.L x i).sc.eps_lt
  have h1 := S.2.1
  simp only [SizeM, szTh] at h1
  have hkey : (Fm.L x i).sc.x ^ (-((Fm.L x i).sc.eps / 100)) *
      Real.sqrt ((Fm.L x i).sc.x * (Fm.L x i).sc.delta1)
      = (Fm.L x i).sc.x ^ (-((Fm.L x i).sc.eps / 100) + (1 + -((Fm.L x i).sc.eps / 8)) * (1 / 2)) := by
    simp only [Formalism.BasicNotions.Scale.delta1]
    rw [Real.sqrt_eq_rpow, show (Fm.L x i).sc.x * (Fm.L x i).sc.x ^ (-((Fm.L x i).sc.eps / 8)) =
      (Fm.L x i).sc.x ^ (1 + -((Fm.L x i).sc.eps / 8)) by
      rw [Real.rpow_add hx0, Real.rpow_one], ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
  have hge : (Fm.L x i).sc.x ^ ((1 : ℝ) / 4) ≤
      (Fm.L x i).sc.x ^ (-((Fm.L x i).sc.eps / 100) + (1 + -((Fm.L x i).sc.eps / 8)) * (1 / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hK4 : max K 44 ≤ (Fm.L x i).sc.x ^ ((1 : ℝ) / 4) := by
    have h2 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (max K 44) ^ 4) hx
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK'] at h2
    norm_num at h2
    exact max_le h2.1 h2.2
  linarith [h1.1, le_max_left K 44]

theorem family_log_gamma_bound {eps : ℝ} (Fm : FamP eps) : StandardLattice.FamilyLogGammaBound Fm := by
  intro x hx i u
  obtain ⟨-, -, -, ⟨-, hG, -⟩, -⟩ := Fm.sizes x hx i
  have hk3 : (3 : ℝ) ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    exact_mod_cast (by omega : 3 ≤ (Fm.D x i).R.k)
  have hf1 : (1 : ℝ) ≤ (Fm.D x i).R.f := by
    have : 1 ≤ (Fm.D x i).R.f := by
      have h1 : (Fm.D x i).R.f = 2 * (Fm.D x i).R.ord := rfl
      have h2 := (Fm.D x i).R.ord_pos
      omega
    exact_mod_cast this
  rw [div_le_one (by nlinarith), (Fm.L x i).Gam_eq u]
  nlinarith

end Formalism.MainNotions.GlobalTheoryTheory
