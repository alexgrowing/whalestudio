import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NonvanishingSectionCondition
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

section Run

variable (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L)

def h0R (T : ParamsT D L P) : ℝ := 4 * (T.TO : ℝ) ^ 2 + D.R.t + 1

theorem two_mul_order_sq_le_length : 2 * (T.TO : ℝ) ^ 2 ≤ ((runOf T S hZ).kl : ℝ) := by
  have hR := rn_of T S hZ
  have h1 := hR.sq_mul_sq_le; have h4 := hR.forty_eight_le_constant
  have h5 : 2 * (T.TO : ℝ) ^ 2 ≤ ((D.R.f : ℝ) * D.R.r) ^ 2 * (T.TO : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ ((D.R.f : ℝ) * D.R.r) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  linarith [b_le_kl T S hZ]

theorem A_le_kf : (D.R.f : ℝ) * D.R.r ≤ 2 * ((D.R.k : ℝ) * D.R.f) := by
  have h1 : D.R.r ≤ 2 * D.R.k := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have h2 : (D.R.r : ℝ) ≤ 2 * (D.R.k : ℝ) := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  linarith

theorem setCn_of (B : WeightFamilies.Prov D) (hO : OPO L B) (hDom : DomAt D L D.R.m T.nWn 1000) :
    Inh.SetCn L B 10 1000 (runOf T S hZ).ka (runOf T S hZ).wL (runOf T S hZ).wF T.TO T.nP T.nWn (h0R T) := by
  have hR := rn_of T S hZ
  have hkl := two_mul_order_sq_le_length T S hZ
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hb := hR.b_pos
  have hAk := A_le_kf (D := D)
  have hTO1 := hR.one_le_order_alt
  have hAkb : ((D.R.f : ℝ) * D.R.r) * L.sc.b ≤ 2 * ((D.R.k : ℝ) * D.R.f) * L.sc.b :=
    mul_le_mul_of_nonneg_right hAk hb.le
  have hkfb : 0 ≤ (D.R.k : ℝ) * D.R.f * L.sc.b := by positivity
  refine ⟨rfl, (runOf T S hZ).gapP, (runOf T S hZ).gapM, le_rfl, fun τ => ?_, fun τ i h => ?_,
    fun τ i h => (runOf T S hZ).lastM _ τ i h, ?_, T.even_nP₂, T.nP_ge, T.nW_lo.2.2, ?_, T.nW_lo.1, T.split,
    (runOf T S hZ).isL, (runOf T S hZ).isF, ?_, (runOf T S hZ).T_pos, ?_, ?_, ?_, T.nW_40, ?_, ?_, hO, hDom⟩
  · rw [RunN.ncAt_ka]
    push_cast
    unfold h0R
    nlinarith [sq_nonneg (T.TO : ℝ)]
  · rw [RunN.ka_last _ τ i h]
    unfold h0R
    linarith
  · have := ka_le T S hZ
    linarith
  · unfold sizeConstantAtParamsWeight
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · rw [le_div_iff₀ (by linarith)]
    have := wL_le T S hZ
    linarith
  · rw [dm_eq T]; have := T.TO_40; omega
  · rw [dm_eq T]; exact T.TO_40
  · rw [dm_eq T]; exact T.TO_nW
  · rw [baseDegree_at_lift_index]
    have h := T.order_ge_rank_bound
    have e : g0 D = 2 * 5 ^ 4 * D.R.r := rfl
    rw [e]
    have : 2 * (2 * 5 ^ 4 * D.R.r) * 1 ≤ 2 * (2 * 5 ^ 4 * D.R.r) * (T.Dp + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [dm_eq T]; exact T.TO_11D2

theorem fourth_hypothesis_of_params : L.sc.b ≤ (runOf T S hZ).ka.size ∧ (T.TO : ℝ) * (runOf T S hZ).wL.size ≤ 2 * (runOf T S hZ).ka.size ∧
    (runOf T S hZ).wF.size ≤ ((WeightFamilies.dimY D D.R.m : ℝ) + 2) * (runOf T S hZ).wL.size + 5 * D.R.f * (D.R.r : ℝ) ^ 2 * T.TO ∧
    WeightFamilies.PPv D L T.CP T.eP ^ 3 * (T.TO : ℝ) ^ 2 ≤ L.sc.b ∧ WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP ≤ L.sc.b ∧
    (∀ i, 2 * DF (runOf T S hZ).ka + 2 < D.host.g i) := by
  have hR := rn_of T S hZ
  have hbk := b_le_ka T S hZ
  have hTb : (T.TO : ℝ) ≤ L.sc.b := hR.toBs.TO_le_sb.trans hR.toBs.sb_le_b
  refine ⟨hbk, ?_, ?_, ?_, ?_, fun i => ?_⟩
  · have := (runOf T S hZ).T_wL_le
    have e : ((runOf T S hZ).T : ℝ) = (T.TO : ℝ) := rfl
    rw [e] at this
    linarith
  · have h := (runOf T S hZ).wF_size_le
    have e : ((runOf T S hZ).nP : ℝ) = (T.nP : ℝ) := rfl
    rw [e] at h
    have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f_ge D
    have hr := hR.r6; have hT := hR.one_le_order_alt; have hn := hR.nPW; have hn2 := hR.nW_le
    have a0 : (0 : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by positivity
    have a1 : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * 1 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * T.TO := mul_le_mul_of_nonneg_left hT a0
    have a2 : (D.R.f : ℝ) * D.R.r * T.nP ≤ (D.R.f : ℝ) * D.R.r * T.TO :=
      mul_le_mul_of_nonneg_left (hn.trans hn2) (by positivity)
    have a3 : (D.R.f : ℝ) * D.R.r * T.TO ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * T.TO := by
      have : (D.R.f : ℝ) * D.R.r ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have a4 : (1 : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by nlinarith
    have e2 : ((Dm D : ℕ) : ℝ) = (WeightFamilies.dimY D D.R.m : ℝ) := rfl
    rw [e2] at h
    nlinarith
  · rw [WeightFamilies.PPv_rec T]
    exact hR.h32.trans hR.toBs.sb_le_b
  · rw [WeightFamilies.PPv_rec T, eRR, ← hR.sb_sq]
    exact mul_le_mul (hR.toBs.rd_pow_le (by norm_num)) hR.toBs.PP_le_sb hR.PP_pos.le hR.sb_pos.le
  · have h1 : (DF (runOf T S hZ).ka : ℝ) ≤ 4 * ((D.R.f : ℝ) * D.R.r) * L.sc.b :=
      (DF_le_size _).trans (ka_le T S hZ)
    have h2 := hR.g_gt h1 (g_ge P i)
    exact_mod_cast h2

theorem lk_bounds : 1 ≤ 1 + Real.log (runOf T S hZ).ka.size ∧ 1 + Real.log (runOf T S hZ).ka.size ≤ 6 * zBase L := by
  have hR := rn_of T S hZ
  have h1 := WeightFamilies.Wt.one_le_size (runOf T S hZ).ka
  have h2 := ka_le T S hZ
  have hA := hR.forty_eight_le_constant
  have hb := hR.b_pos
  constructor
  · have := Real.log_nonneg h1; linarith
  · have a1 : Real.log (runOf T S hZ).ka.size ≤ Real.log (4 * ((D.R.f : ℝ) * D.R.r) * L.sc.b) :=
      Real.log_le_log (by linarith) h2
    have a2 : Real.log (4 * ((D.R.f : ℝ) * D.R.r) * L.sc.b) = Real.log (4 * ((D.R.f : ℝ) * D.R.r)) + L.sc.L := by
      rw [Real.log_mul (by positivity) hb.ne']
      congr 1
      exact Real.log_exp _
    have a3 : Real.log (4 * ((D.R.f : ℝ) * D.R.r)) ≤ 4 * ((D.R.f : ℝ) * D.R.r) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have a4 := A_le_Z L
    have a5 : L.sc.L ≤ zBase L := by
      unfold zBase
      have := one_le_L L
      nlinarith
    linarith

theorem poly_of (B : WeightFamilies.Prov D) (hOb : WeightFamilies.Obound B L 1 2) :
    PolyDom (j := D.R.m) D B L Kc0 (NonvanishingSectionCondition T) T.CP T.eP 2 1 2 1 1 0 (1 / 2) (1 / 2) 0
      (WeightFamilies.PPv D L 1 1 * (1 + Real.log (runOf T S hZ).ka.size)) (runOf T S hZ).ka := by
  have hR := rn_of T S hZ
  have hZ1 : (1 : ℝ) ≤ zBase L := le_trans (by norm_num) hZ
  have hPP := hR.toBs.PP_ge
  have hPP60 : (100 : ℝ) ≤ T.PP := le_trans (by norm_num) hPP
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f_ge D
  have hDp : (1 : ℝ) ≤ (T.Dp : ℝ) := by
    have := Inh.dimY_pos' D (Inh.h1m D)
    rw [dm_eq T] at this
    exact_mod_cast this
  obtain ⟨l1, l2⟩ := lk_bounds T S hZ
  obtain ⟨p1, p2⟩ := polyA hZ (zBase_pow_twelve_le T hZ1) (growthZero_le_thirty_zBase P) (PO_le L) l1 l2 hDp
  have hPP2 : T.PP ≤ T.PP ^ 2 := by nlinarith
  refine ⟨le_rfl, by norm_num, le_rfl, by norm_num, growthZero_nonneg L, hOb, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, le_rfl, le_rfl,
    le_rfl, ?_⟩
  · show WeightFamilies.RRv D 2 * D.host.rdE ^ 2 ≤ WeightFamilies.RRv D 2 ^ 2
    rw [eRR]; exact le_of_eq (by ring)
  · rw [WeightFamilies.PPv_rec T]; linarith
  · rw [WeightFamilies.PPv_rec T]
    show 4 * (10 : ℝ) ≤ _
    nlinarith
  · rw [WeightFamilies.PPv_rec T]; linarith
  · rw [WeightFamilies.PPv_rec T]; linarith
  · rw [WeightFamilies.PPv_rec T, growth_at_one_eq_zBase]
    exact p1
  · rw [WeightFamilies.PPv_rec T, growth_at_one_eq_zBase, dm_eq T]
    exact p2
  · rw [WeightFamilies.PPv_rec T]; linarith

theorem numRun_of (hCnW : P.CnW = 10) (hg : ∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) (hx : (10 : ℝ) ^ 60 ≤ L.sc.x)
    (e : 𝓞 D.host.E ≃+* D.what₂.O) (Sg : ∀ j, WeightFamilies.Wt D j → Prop) (τ0 : D.what₂.Tau) :
    Inh.NumRun L (Inh.provS D D.host.E e Sg) Kc0 (NonvanishingSectionCondition T) 1 2 1 1 T.CP T.eP 2 L.Ct 0 (1 / 2) (1 / 2) 0
      (WeightFamilies.PPv D L 1 1 * (1 + Real.log (runOf T S hZ).ka.size))
      (runOf T S hZ).ka (runOf T S hZ).wL (runOf T S hZ).wF T.TO T.nP T.nWn (h0R T) τ0 where
  parA := parA_of P S hg hx
  setC := setCn_of T S hZ _ (opo_of P e Sg) (domAt_of P T S hCnW hg hx)
  h3 := third_hypothesis_of_params T S hZ
  h4 := fourth_hypothesis_of_params T S hZ
  g2 := ⟨(runOf T S hZ).w2, (runOf T S hZ).run_isSecondWeight⟩
  Tx := T.TO_poly
  poly := poly_of T S hZ _ (obound_of P e Sg)
  page := le_rfl
  pd := by
    rw [growth_at_one_eq_zBase]
    have := (lk_bounds T S hZ).1
    have hZ0 : (0 : ℝ) ≤ zBase L := le_trans (by positivity) hZ
    exact mul_nonneg hZ0 (by linarith)

end Run

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end
