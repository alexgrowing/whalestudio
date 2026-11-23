import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.S.UnitaryVolumeMass Formalism.MainNotions.S.Bridge

theorem tf_m_eq (D : D7) : D.R.m = 2 * D.R.rS + 2 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  simp only [Ranks.rS]
  omega

structure TfFacts (D : D7) (large₂ : SizeData₂ D) (C' Cl Cu C0 : ℝ) : Prop where
  hGam : 8 * large₂.CGam ≤ C'
  hk : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k
  hfk : D.R.f ≤ D.R.k
  hb1 : ∀ τ j, 1 ≤ j → j ≤ D.R.m → Cl * ((D.R.m : ℝ) * D.R.k * D.s.Del) ≤ bOne D τ j
  hg0 : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g 0 : ℝ)
  hg1 : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g 1 : ℝ)
  hbk : ∀ τ j, 1 ≤ j → j ≤ D.R.m → (D.R.k : ℝ) ^ Cl ≤ bOne D τ j
  hu1 : ∀ u τ, uOne D u τ 1 ≤ large₂.sc.b ^ Cu
  hv : 1 ≤ D.host.v
  hDel : ((D.R.k : ℝ) * D.R.f * large₂.sc.L) ^ Cl ≤ D.s.Del
  hCl0 : 0 < Cl
  dv : ∀ τ l, 1 ≤ l → l ≤ D.R.k - 1 → 0 ≤ vOne D τ l
  du : ∀ u τ, 4 * (D.R.k : ℝ) * D.s.Del ≤ uOne D u τ 1 - vOne D τ 1
  dn : ∀ u τ, ¬ IsTop D τ → uOne D u τ 1 - vOne D τ 1 ≤ 8 * (D.R.k : ℝ) * D.s.Del
  dt : ∀ τ, IsTop D τ → 3 ≤ bOne D τ 1 - bTop D τ ∧ bOne D τ 1 / 2 ≤ bTop D τ
  dw : ∀ u, (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar / C0 ≤ (D.duS u : ℝ)
  hC0 : 1 ≤ C0

theorem tfFacts_of {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (h : Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) : TfFacts D large₂ C' Cl Cu C0 := by
  obtain ⟨hH, hD, hC0⟩ := h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25⟩ := hH
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩ := hD
  exact
    { hGam := a1, hk := a2, hfk := a4, hb1 := a8, hg0 := a12, hg1 := a14
      hbk := fun τ j h1 h2 => le_trans (le_max_left _ _) (a16 τ j h1 h2).1
      hu1 := a18, hv := a19, hDel := a20, hCl0 := a25
      dv := fun τ l h1 h2 => (d1 τ l h1 h2).1
      du := d3, dn := d4, dt := d6, dw := fun u => (d10 u).1, hC0 := hC0 }

section Rec

variable {D : D7} {large₂ : SizeData₂ D} {C' Cl Cu C0 : ℝ}

theorem five_le_k_real (D : D7) : (5 : ℝ) ≤ D.R.k := by
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  exact_mod_cast (by omega : 5 ≤ D.R.k)

theorem one_le_scale_log (large₂ : SizeData₂ D) : 1 ≤ large₂.sc.L := by
  unfold Scale.L
  exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le

theorem one_le_scale_base_alt (large₂ : SizeData₂ D) : 1 ≤ large₂.sc.b := by
  unfold Scale.b
  exact Real.one_le_exp (le_trans zero_le_one (one_le_scale_log large₂))

theorem two_le_degree_bis (D : D7) : (2 : ℝ) ≤ D.R.f := by
  have : 2 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    have := D.R.ord_pos
    omega
  exact_mod_cast this

theorem TfFacts.Del1 (F : TfFacts D large₂ C' Cl Cu C0) : (1 : ℝ) ≤ D.s.Del := by
  refine le_trans ?_ F.hDel
  refine Real.one_le_rpow ?_ F.hCl0.le
  have h1 := five_le_k_real D
  have h2 := two_le_degree_bis D
  have h3 := one_le_scale_log large₂
  nlinarith [mul_le_mul h1 h2 (by norm_num) (by linarith)]

theorem tf_logk (D : D7) : 1 ≤ Real.log D.R.k := by
  rw [Real.le_log_iff_exp_le (by linarith [five_le_k_real D])]
  have := Real.exp_one_lt_d9
  linarith [five_le_k_real D]

theorem TfFacts.aEff_bd (F : TfFacts D large₂ C' Cl Cu C0) (hCl : 4 ≤ Cl) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    0 < aEff D u τ ∧ aEff D u τ ≤ bOne D τ 1 * large₂.sc.b ^ Cu := by
  have hK := five_le_k_real D
  have hDel := F.Del1
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hKD : 1 ≤ (D.R.k : ℝ) * D.s.Del := by nlinarith
  have hv1 : 0 ≤ vOne D τ 1 := F.dv τ 1 le_rfl (by have := D.R.m_add_three_le_k; omega)
  have hu := F.du u τ
  have hu1 : 1 ≤ uOne D u τ 1 := by nlinarith
  have hbC : 1 ≤ large₂.sc.b ^ Cu := le_trans hu1 (F.hu1 u τ)
  have hb := F.hb1 τ 1 le_rfl (by have := D.R.two_le_m; omega)
  have hb8 : 8 * ((D.R.k : ℝ) * D.s.Del) ≤ bOne D τ 1 := by
    refine le_trans ?_ hb
    have : (8 : ℝ) ≤ Cl * D.R.m := by nlinarith
    calc 8 * ((D.R.k : ℝ) * D.s.Del) ≤ (Cl * D.R.m) * ((D.R.k : ℝ) * D.s.Del) := by gcongr
      _ = Cl * ((D.R.m : ℝ) * D.R.k * D.s.Del) := by ring
  have hb0 : 0 < bOne D τ 1 := by linarith
  by_cases hT : IsTop D τ
  · rw [aEff, if_pos hT]
    obtain ⟨t1, t2⟩ := F.dt τ hT
    have hbp : 0 < bTop D τ := by linarith
    refine ⟨by positivity, ?_⟩
    refine le_trans (div_le_self (by positivity) hKD) ?_
    rw [mul_comm]
    exact mul_le_mul (by linarith) (F.hu1 u τ) (by linarith) hb0.le
  · rw [aEff, if_neg hT]
    refine ⟨by nlinarith, ?_⟩
    have := F.dn u τ hT
    nlinarith

theorem TfFacts.core (F : TfFacts D large₂ C' Cl Cu C0) {C3 : ℝ} (hCl : 4 ≤ Cl) (hC3 : 2 * C3 ≤ D.R.m)
    (hCu : Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Real.pi ^ (2 * D.R.rS + 1) * (D.R.k : ℝ) ^ (3 * D.R.rS) ≤
      (∏ j ∈ Finset.Icc 1 D.R.m, bOne D τ j) * (D.R.k : ℝ) ^ (-C3) / aEff D u τ := by
  obtain ⟨ha0, ha1⟩ := F.aEff_bd hCl u τ
  have hK := five_le_k_real D
  have hK0 : (0 : ℝ) < D.R.k := by linarith
  have hK1 : (1 : ℝ) ≤ D.R.k := by linarith
  have hm := tf_m_eq D
  have hmR : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2 := by rw [hm]; push_cast; ring

  have hP : ∏ j ∈ Finset.Icc 1 D.R.m, bOne D τ j = bOne D τ 1 * ∏ j ∈ Finset.Ioc 1 D.R.m, bOne D τ j := by
    rw [Finset.Icc_eq_cons_Ioc (by omega : 1 ≤ D.R.m), Finset.prod_cons]
  have hQ : ((D.R.k : ℝ) ^ 4) ^ (2 * D.R.rS + 1) ≤ ∏ j ∈ Finset.Ioc 1 D.R.m, bOne D τ j := by
    have hc : (Finset.Ioc 1 D.R.m).card = 2 * D.R.rS + 1 := by rw [Nat.card_Ioc]; omega
    rw [← hc, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun j _ => by positivity) (fun j hj => ?_)
    rw [Finset.mem_Ioc] at hj
    refine le_trans ?_ (F.hbk τ j (by omega) hj.2)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hK1 (by exact_mod_cast hCl)
  have hb0 : 0 < bOne D τ 1 := by
    have h1 : 0 < large₂.sc.b ^ Cu := Real.rpow_pos_of_pos (by linarith [one_le_scale_base_alt large₂]) _
    by_contra hneg
    have : bOne D τ 1 * large₂.sc.b ^ Cu ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) h1.le
    linarith

  have hpi : Real.pi ^ (2 * D.R.rS + 1) ≤ (D.R.k : ℝ) ^ (2 * D.R.rS + 1) :=
    pow_le_pow_left₀ Real.pi_pos.le (by linarith [Real.pi_le_four]) _
  have hbC : large₂.sc.b ^ Cu ≤ (D.R.k : ℝ) ^ (2 * D.R.rS + 1) := by
    have e1 : large₂.sc.b ^ Cu = Real.exp (Cu * large₂.sc.L) := by
      unfold Scale.b; rw [← Real.exp_mul, mul_comm]
    have e2 : (D.R.k : ℝ) ^ (2 * D.R.rS + 1) = Real.exp (Real.log D.R.k * ((2 * D.R.rS + 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hK0]
    rw [e1, e2, Real.exp_le_exp]
    have h1 := tf_logk D
    have h2 : Cu * large₂.sc.L ≤ ((2 * D.R.rS + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h3 : (0 : ℝ) ≤ ((2 * D.R.rS + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hk3 : (D.R.k : ℝ) ^ C3 ≤ (D.R.k : ℝ) ^ (D.R.rS + 1) := by
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hK1 ?_
    push_cast; linarith
  have hk3pos : 0 < (D.R.k : ℝ) ^ C3 := Real.rpow_pos_of_pos hK0 _
  have hbCpos : 0 < large₂.sc.b ^ Cu := Real.rpow_pos_of_pos (by linarith [one_le_scale_base_alt large₂]) _
  have key : Real.pi ^ (2 * D.R.rS + 1) * (D.R.k : ℝ) ^ (3 * D.R.rS) * large₂.sc.b ^ Cu * (D.R.k : ℝ) ^ C3 ≤
      ∏ j ∈ Finset.Ioc 1 D.R.m, bOne D τ j := by
    calc Real.pi ^ (2 * D.R.rS + 1) * (D.R.k : ℝ) ^ (3 * D.R.rS) * large₂.sc.b ^ Cu * (D.R.k : ℝ) ^ C3
        ≤ (D.R.k : ℝ) ^ (2 * D.R.rS + 1) * (D.R.k : ℝ) ^ (3 * D.R.rS) * (D.R.k : ℝ) ^ (2 * D.R.rS + 1) *
            (D.R.k : ℝ) ^ (D.R.rS + 1) := by gcongr
      _ = (D.R.k : ℝ) ^ (8 * D.R.rS + 3) := by ring
      _ ≤ (D.R.k : ℝ) ^ (8 * D.R.rS + 4) := pow_le_pow_right₀ hK1 (by omega)
      _ = ((D.R.k : ℝ) ^ 4) ^ (2 * D.R.rS + 1) := by ring
      _ ≤ _ := hQ
  rw [le_div_iff₀ ha0, hP, Real.rpow_neg hK0.le]
  have hA : 0 ≤ Real.pi ^ (2 * D.R.rS + 1) * (D.R.k : ℝ) ^ (3 * D.R.rS) := by positivity
  calc Real.pi ^ (2 * D.R.rS + 1) * (D.R.k : ℝ) ^ (3 * D.R.rS) * aEff D u τ
      ≤ Real.pi ^ (2 * D.R.rS + 1) * (D.R.k : ℝ) ^ (3 * D.R.rS) * (bOne D τ 1 * large₂.sc.b ^ Cu) := by gcongr
    _ = bOne D τ 1 * (Real.pi ^ (2 * D.R.rS + 1) * (D.R.k : ℝ) ^ (3 * D.R.rS) * large₂.sc.b ^ Cu * (D.R.k : ℝ) ^ C3) *
          ((D.R.k : ℝ) ^ C3)⁻¹ := by field_simp
    _ ≤ bOne D τ 1 * (∏ j ∈ Finset.Ioc 1 D.R.m, bOne D τ j) * ((D.R.k : ℝ) ^ C3)⁻¹ := by gcongr

end Rec

section Rec2

variable {D : D7} {large₂ : SizeData₂ D} {C' Cl Cu C0 : ℝ}

theorem tf_ka (D : D7) (hv : 1 ≤ D.host.v) : 0 < D.host.ka ∧ D.host.ka ≤ Real.pi := by
  unfold Host.ka
  exact ⟨div_pos Real.pi_pos (by linarith), div_le_self Real.pi_pos.le hv⟩

theorem TfFacts.gg_ge (F : TfFacts D large₂ C' Cl Cu C0) : (D.R.k : ℝ) ^ 2 ≤ gg D := by
  have hK := five_le_k_real D
  have hb := one_le_scale_base_alt large₂
  have h1 : (D.R.k : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    have h2 : (D.R.k : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
    have h3 : (1 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by linarith
    calc (D.R.k : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := h2
      _ = ((D.R.k : ℝ) * large₂.sc.b) ^ 1 := (pow_one _).symm
      _ ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := pow_le_pow_right₀ h3 (by norm_num)
  unfold gg
  rw [sq]
  exact mul_le_mul (le_trans h1 F.hg0) (le_trans h1 F.hg1) (by linarith) (by linarith [le_trans h1 F.hg0])

theorem TfFacts.tcrit_ge (F : TfFacts D large₂ C' Cl Cu C0) {C3 : ℝ} (hCl : 4 ≤ Cl) (hC3 : 2 * C3 ≤ D.R.m)
    (hCu : Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1) (hD : cTvD D C3) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    gg D ^ (2 * D.R.rS + 2) * (D.host.ka ^ (2 * D.R.rS + 1))⁻¹ *
      (Real.pi ^ (2 * D.R.rS + 1) * (D.R.k : ℝ) ^ (3 * D.R.rS)) ≤ Tcrit D u τ := by
  have h := hD u τ
  have hc := F.core hCl hC3 hCu u τ
  obtain ⟨hka0, _⟩ := tf_ka D F.hv
  have hg0 : 0 < gg D := lt_of_lt_of_le (by have := five_le_k_real D; positivity) F.gg_ge
  have hm := tf_m_eq D
  have e1 : D.host.ka ^ (-((D.R.m : ℝ) - 1)) = (D.host.ka ^ (2 * D.R.rS + 1))⁻¹ := by
    rw [Real.rpow_neg hka0.le, ← Real.rpow_natCast]
    congr 2
    rw [hm]; push_cast; ring
  rw [e1, hm] at h
  refine le_trans ?_ h
  rw [hm] at hc
  calc gg D ^ (2 * D.R.rS + 2) * (D.host.ka ^ (2 * D.R.rS + 1))⁻¹ *
        (Real.pi ^ (2 * D.R.rS + 1) * (D.R.k : ℝ) ^ (3 * D.R.rS))
      ≤ gg D ^ (2 * D.R.rS + 2) * (D.host.ka ^ (2 * D.R.rS + 1))⁻¹ *
        ((∏ j ∈ Finset.Icc 1 (2 * D.R.rS + 2), bOne D τ j) * (D.R.k : ℝ) ^ (-C3) / aEff D u τ) := by gcongr
    _ = _ := by ring

theorem TfFacts.tcritLow (F : TfFacts D large₂ C' Cl Cu C0) {C3 : ℝ} (hCl : 4 ≤ Cl) (hC3 : 2 * C3 ≤ D.R.m)
    (hCu : Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1) (hD : cTvD D C3) (w : D.what₂.Word) (τ : D.what₂.Tau) :
    (D.R.k : ℝ) ^ (3 * D.R.rS) ≤ gg D ^ (-(D.R.m : ℝ)) * Tcrit D w τ := by
  have h := F.tcrit_ge hCl hC3 hCu hD w τ
  obtain ⟨hka0, hka1⟩ := tf_ka D F.hv
  have hg0 : 0 < gg D := lt_of_lt_of_le (by have := five_le_k_real D; positivity) F.gg_ge
  have hm := tf_m_eq D
  have e1 : gg D ^ (-(D.R.m : ℝ)) = (gg D ^ (2 * D.R.rS + 2))⁻¹ := by
    rw [Real.rpow_neg hg0.le, Real.rpow_natCast, hm]
  rw [e1]
  have hr : 1 ≤ (D.host.ka ^ (2 * D.R.rS + 1))⁻¹ * Real.pi ^ (2 * D.R.rS + 1) := by
    rw [inv_mul_eq_div, one_le_div (by positivity)]
    exact pow_le_pow_left₀ hka0.le hka1 _
  have hK0 : (0 : ℝ) ≤ (D.R.k : ℝ) ^ (3 * D.R.rS) := by positivity
  calc (D.R.k : ℝ) ^ (3 * D.R.rS) = 1 * (D.R.k : ℝ) ^ (3 * D.R.rS) := (one_mul _).symm
    _ ≤ ((D.host.ka ^ (2 * D.R.rS + 1))⁻¹ * Real.pi ^ (2 * D.R.rS + 1)) * (D.R.k : ℝ) ^ (3 * D.R.rS) := by gcongr
    _ = (gg D ^ (2 * D.R.rS + 2))⁻¹ * (gg D ^ (2 * D.R.rS + 2) * (D.host.ka ^ (2 * D.R.rS + 1))⁻¹ *
          (Real.pi ^ (2 * D.R.rS + 1) * (D.R.k : ℝ) ^ (3 * D.R.rS))) := by field_simp
    _ ≤ (gg D ^ (2 * D.R.rS + 2))⁻¹ * Tcrit D w τ := by gcongr

theorem TfFacts.frame_tcrit (F : TfFacts D large₂ C' Cl Cu C0) {C3 : ℝ} (hCl : 4 ≤ Cl) (hC3 : 2 * C3 ≤ D.R.m)
    (hCu : Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1) (hD : cTvD D C3) (w : D.what₂.Word) (τ : D.what₂.Tau) :
    gg D ^ 2 ≤ kaS D ^ (2 * D.R.rS) * Tcrit D w τ := by
  have h := F.tcrit_ge hCl hC3 hCu hD w τ
  obtain ⟨hka0, hka1⟩ := tf_ka D F.hv
  have hg0 : 0 < gg D := lt_of_lt_of_le (by have := five_le_k_real D; positivity) F.gg_ge
  have hK1 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ (3 * D.R.rS) := one_le_pow₀ (by linarith [five_le_k_real D])
  have hpi : D.host.ka ≤ Real.pi ^ (2 * D.R.rS + 1) := by
    refine le_trans hka1 ?_
    calc Real.pi = Real.pi ^ 1 := (pow_one _).symm
      _ ≤ Real.pi ^ (2 * D.R.rS + 1) := pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) (by omega)
  have hs0 : 0 < kaS D ^ (2 * D.R.rS) := by unfold kaS; positivity
  have hx : D.host.ka ≤ Real.pi ^ (2 * D.R.rS + 1) * (D.R.k : ℝ) ^ (3 * D.R.rS) := by
    have : 0 < Real.pi ^ (2 * D.R.rS + 1) := by positivity
    nlinarith
  calc gg D ^ 2 = kaS D ^ (2 * D.R.rS) * (gg D ^ (2 * D.R.rS + 2) * (D.host.ka ^ (2 * D.R.rS + 1))⁻¹ * D.host.ka) := by
        unfold kaS; rw [div_pow]; field_simp; ring
    _ ≤ kaS D ^ (2 * D.R.rS) * (gg D ^ (2 * D.R.rS + 2) * (D.host.ka ^ (2 * D.R.rS + 1))⁻¹ *
          (Real.pi ^ (2 * D.R.rS + 1) * (D.R.k : ℝ) ^ (3 * D.R.rS))) := by gcongr
    _ ≤ kaS D ^ (2 * D.R.rS) * Tcrit D w τ := by gcongr

end Rec2

section Rec3

variable {D : D7} {large₂ : SizeData₂ D} {C' Cl Cu C0 : ℝ}

theorem TfFacts.E_le (F : TfFacts D large₂ C' Cl Cu C0) : (D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k) ≤ 8 := by
  have h1 : (D.R.f : ℝ) ≤ (2 : ℝ) ^ D.R.k := by
    have : D.R.f ≤ 2 ^ D.R.k := le_trans F.hfk (Nat.lt_two_pow_self).le
    exact_mod_cast this
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ D.R.k := by positivity
  have h3 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  rw [h3, ← mul_div_assoc, div_le_iff₀ h2]
  nlinarith

theorem TfFacts.Gam_le (F : TfFacts D large₂ C' Cl Cu C0) (u : D.what₂.Word) :
    (D.mem u).A.GamP ^ 2 ≤ Real.exp ((D.R.k : ℝ) / 4) := by
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have e : (D.mem u).A.GamP = Real.exp (large₂.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by
    rw [← large₂.Gam_eq u, Real.exp_log hG]
  rw [e, sq, ← Real.exp_add, Real.exp_le_exp]
  have hx : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
    have := one_le_scale_log large₂
    positivity
  have h1 := F.hGam
  have h2 := F.hk
  nlinarith

theorem TfFacts.ratio_le (F : TfFacts D large₂ C' Cl Cu C0) (u : D.what₂.Word) :
    D.what₂.Dstar / (D.duS u : ℝ) ≤ C0 * (D.mem u).A.GamP ^ 2 := by
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hDs : 0 < D.what₂.Dstar := by rw [← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos
  have hC0 : 0 < C0 := lt_of_lt_of_le one_pos F.hC0
  have h := F.dw u
  rw [zpow_neg, zpow_ofNat] at h
  have hd : 0 < (D.duS u : ℝ) := lt_of_lt_of_le (by positivity) h
  rw [div_le_iff₀ hd]
  rw [div_le_iff₀ hC0, inv_mul_le_iff₀ (by positivity)] at h
  linarith

theorem TfFacts.tframe (F : TfFacts D large₂ C' Cl Cu C0) {C3 : ℝ} (hCl : 4 ≤ Cl) (hC3 : 2 * C3 ≤ D.R.m)
    (hCu : Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1) (hA : cTvA D) (hD : cTvD D C3) (hk : C0 * Real.exp 8 ≤ D.R.k)
    (w : D.what₂.Word) : 1 ≤ Tr D w * kaS D ^ (2 * D.R.rS) := by
  by_contra hlt0
  have hlt := not_le.1 hlt0
  have hK := five_le_k_real D
  have hgg := F.gg_ge
  have hg0 : 0 < gg D := lt_of_lt_of_le (by positivity) hgg
  have hT0 : 0 < Tr D w := by
    unfold Tr
    exact_mod_cast (D.mem w).A.T_prime.pos
  obtain ⟨hka0, _⟩ := tf_ka D F.hv
  have hs0 : 0 < kaS D ^ (2 * D.R.rS) := by unfold kaS; positivity
  have hτ : ∀ τ, gg D ^ 2 ≤ Tcrit D w τ / Tr D w := by
    intro τ
    have h1 := F.frame_tcrit hCl hC3 hCu hD w τ
    have hTc : 0 < Tcrit D w τ := by
      by_contra hn
      have : kaS D ^ (2 * D.R.rS) * Tcrit D w τ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0.le (not_lt.1 hn)
      have : 0 < gg D ^ 2 := by positivity
      linarith
    rw [le_div_iff₀ hT0]
    calc gg D ^ 2 * Tr D w ≤ (kaS D ^ (2 * D.R.rS) * Tcrit D w τ) * Tr D w := by gcongr
      _ = (Tr D w * kaS D ^ (2 * D.R.rS)) * Tcrit D w τ := by ring
      _ ≤ 1 * Tcrit D w τ := by gcongr
      _ = Tcrit D w τ := one_mul _
  have hg1 : 1 ≤ (gg D ^ 2) ^ D.R.k := one_le_pow₀ (one_le_pow₀ (by nlinarith))
  have hprod : (gg D ^ 2) ^ D.R.k ≤ ∏ τ, (Tcrit D w τ / Tr D w) ^ D.R.k := by
    have h1 : ∏ _τ : D.what₂.Tau, (gg D ^ 2) ^ D.R.k ≤ ∏ τ, (Tcrit D w τ / Tr D w) ^ D.R.k :=
      Finset.prod_le_prod (fun τ _ => by positivity) (fun τ _ => pow_le_pow_left₀ (by positivity) (hτ τ) _)
    refine le_trans ?_ h1
    rw [Finset.prod_const, Finset.card_univ, D.what₂.card_Tau]
    have hf : 1 ≤ D.R.f := by
      have := two_le_degree_bis D
      have h2 : (2 : ℕ) ≤ D.R.f := by exact_mod_cast this
      omega
    calc (gg D ^ 2) ^ D.R.k = ((gg D ^ 2) ^ D.R.k) ^ 1 := (pow_one _).symm
      _ ≤ ((gg D ^ 2) ^ D.R.k) ^ D.R.f := pow_le_pow_right₀ hg1 hf
  have hup : ∏ τ, (Tcrit D w τ / Tr D w) ^ D.R.k ≤ Real.exp 8 * (C0 * Real.exp ((D.R.k : ℝ) / 4)) := by
    have h1 := (hA w).1
    have h2 := F.ratio_le w
    have h3 := F.Gam_le w
    have h4 := F.E_le
    have hC0 : 0 < C0 := lt_of_lt_of_le one_pos F.hC0
    have h5 : D.what₂.Dstar / (D.duS w : ℝ) ≤ C0 * Real.exp ((D.R.k : ℝ) / 4) :=
      le_trans h2 (by gcongr)
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)] at h1
    refine le_trans h1 ?_
    have h6 : Real.exp ((D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k)) ≤ Real.exp 8 := Real.exp_le_exp.2 h4
    have h7 : 0 ≤ D.what₂.Dstar / (D.duS w : ℝ) := by
      have hDs : 0 < D.what₂.Dstar := by rw [← D.Dstar_eq w]; exact (D.mem w).A.Dstar_pos
      positivity
    exact mul_le_mul h6 h5 h7 (Real.exp_pos _).le
  have hk1 : 1 ≤ D.R.k := by
    have h2 : (5 : ℕ) ≤ D.R.k := by exact_mod_cast hK
    omega
  have hlow1 : C0 * Real.exp 8 < gg D ^ D.R.k := by
    have h1 : gg D ≤ gg D ^ D.R.k := by
      calc gg D = gg D ^ 1 := (pow_one _).symm
        _ ≤ gg D ^ D.R.k := pow_le_pow_right₀ (by nlinarith) hk1
    nlinarith
  have hlow2 : Real.exp ((D.R.k : ℝ) / 4) ≤ gg D ^ D.R.k := by
    have h1 : Real.exp 1 ≤ gg D := by
      have := Real.exp_one_lt_d9
      nlinarith
    calc Real.exp ((D.R.k : ℝ) / 4) ≤ Real.exp ((D.R.k : ℝ) * 1) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp 1 ^ D.R.k := Real.exp_nat_mul 1 D.R.k
      _ ≤ gg D ^ D.R.k := pow_le_pow_left₀ (Real.exp_pos _).le h1 _
  have hfin : Real.exp 8 * (C0 * Real.exp ((D.R.k : ℝ) / 4)) < (gg D ^ 2) ^ D.R.k := by
    have e : (gg D ^ 2) ^ D.R.k = gg D ^ D.R.k * gg D ^ D.R.k := by ring
    rw [e]
    have hpos : 0 < Real.exp ((D.R.k : ℝ) / 4) := Real.exp_pos _
    calc Real.exp 8 * (C0 * Real.exp ((D.R.k : ℝ) / 4)) = (C0 * Real.exp 8) * Real.exp ((D.R.k : ℝ) / 4) := by ring
      _ < gg D ^ D.R.k * Real.exp ((D.R.k : ℝ) / 4) := by gcongr
      _ ≤ gg D ^ D.R.k * gg D ^ D.R.k := by gcongr
  linarith

end Rec3

section Fam

variable {eps : ℝ} (Fm : FamP eps)

theorem tf_ev_CL (C : ℝ) : ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
    C * (Fm.L x i).sc.L ≤ ((Fm.D x i).R.m : ℝ) - 1 := by
  have he := eps_pos Fm
  have hl := eps_lt Fm
  obtain ⟨a, ha1, ha⟩ := ev_rpow (show (0 : ℝ) < 1 / 4 - eps by linarith) (|C| + 1)
  refine ⟨a, fun x hx hx1 i => ?_⟩
  have h1 : 1 < x := one_lt_of Fm hx1
  have h0 : 0 < x := by linarith
  rw [sc_L Fm hx1]
  have hm := m_ge Fm hx1 i
  have hL : 1 ≤ x ^ eps := Real.one_le_rpow h1.le he.le
  have hs : x ^ ((1 : ℝ) / 4) = x ^ eps * x ^ ((1 : ℝ) / 4 - eps) := by
    rw [← Real.rpow_add h0]; congr 1; ring
  have h2 := ha x hx
  have h3 : C ≤ |C| := le_abs_self C
  have h4 : x ^ eps * (|C| + 1) ≤ x ^ ((1 : ℝ) / 4) := by rw [hs]; gcongr
  nlinarith [abs_nonneg C]

theorem TFrame_of_sizes (Cg cb Cu cT CT C0 C3 : ℝ) (hCl : 4 ≤ sCl Fm)
    (hA : OwnEv Fm fun C' Cl x i => Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → cTvA (Fm.D x i))
    (h : OwnEv Fm fun C' Cl x i => Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → cTvD (Fm.D x i) C3) :
    PX.TFrame Fm Cg cb Cu cT CT C0 := by
  obtain ⟨x1, HA⟩ := hA
  obtain ⟨x2, H⟩ := h
  obtain ⟨x3, _, H3⟩ := ev_m Fm (2 * C3)
  obtain ⟨x4, H4⟩ := tf_ev_CL Fm Cu
  obtain ⟨x5, _, H5⟩ := ev_k Fm (C0 * Real.exp 8)
  refine ownEv_intro Fm (max x1 (max x2 (max x3 (max x4 x5)))) (fun x hx hx1 i => ?_)
  have hy1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hr1 := le_trans (le_max_right _ _) hx
  have hy2 : x2 ≤ x := le_trans (le_max_left _ _) hr1
  have hr2 := le_trans (le_max_right _ _) hr1
  have hy3 : x3 ≤ x := le_trans (le_max_left _ _) hr2
  have hr3 := le_trans (le_max_right _ _) hr2
  have hy4 : x4 ≤ x := le_trans (le_max_left _ _) hr3
  have hy5 : x5 ≤ x := le_trans (le_max_right _ _) hr3
  intro hyp w
  exact (tfFacts_of hyp).tframe hCl (H3 x hy3 i) (H4 x hy4 hx1 i) (HA x hy1 i hyp) (H x hy2 i hyp) (H5 x hy5 i) w

theorem level_frame_of_sizes (Cg cb Cu cT CT C0 C3 : ℝ) (hCl : 4 ≤ sCl Fm)
    (hA : LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT) (h : LocalBesselAndTopKernel.LocalSplitExponents Fm C0 Cg cb Cu cT CT C3) :
    PX.TFrame Fm Cg cb Cu cT CT C0 := by
  obtain ⟨x0, HA⟩ := hA
  obtain ⟨x0', H⟩ := h
  exact TFrame_of_sizes Fm Cg cb Cu cT CT C0 C3 hCl
    ⟨x0, fun x hx i hyp => HA x hx i ⟨hyp.2.1, hyp.1, hyp.2.2⟩⟩
    ⟨x0', fun x hx i hyp => H x hx i ⟨hyp.2.1, hyp.1, hyp.2.2⟩⟩

end Fam

section Check

variable {eps : ℝ} (Fm : FamP eps)

end Check

end Formalism.MainNotions.BridgeLemma

end
