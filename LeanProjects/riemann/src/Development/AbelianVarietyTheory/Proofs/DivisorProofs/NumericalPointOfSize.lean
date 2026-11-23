import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaExponentIdentities

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.NumSizes

theorem r_log_div_le (r t q : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hq : 4 * t * r + 1 < q) :
    (r : ℝ) * Real.log q / ((q : ℝ) - 1) ≤ 2 * Real.log 6 + 4 * Real.log ((r : ℝ) + t) := by
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  set Q : ℝ := 4 * t * r + 2 with hQ
  have hqQ : Q ≤ q := by rw [hQ]; exact_mod_cast (by omega : 4 * t * r + 2 ≤ q)
  have hQ6 : (6:ℝ) ≤ Q := by rw [hQ]; nlinarith
  have he : Real.exp 1 ≤ Q := by have := Real.exp_one_lt_d9; linarith
  have hant : Real.log q / q ≤ Real.log Q / Q :=
    Real.log_div_self_antitoneOn (Set.mem_Ici.2 he) (Set.mem_Ici.2 (he.trans hqQ)) hqQ
  have hq0 : (0:ℝ) < q := by linarith
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have s1 : (r : ℝ) * Real.log q / ((q : ℝ) - 1) ≤ (r : ℝ) * Real.log q / ((q : ℝ) / 2) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have s2 : (r : ℝ) * Real.log q / ((q : ℝ) / 2) = 2 * r * (Real.log q / q) := by
    field_simp
  have s3 : 2 * (r : ℝ) * (Real.log Q / Q) ≤ 2 * Real.log Q := by
    have hrQ : (r : ℝ) ≤ Q := by rw [hQ]; nlinarith
    have hQ0 : (0:ℝ) < Q := by linarith
    rw [mul_div_assoc', div_le_iff₀ hQ0]
    nlinarith
  have s4 : Real.log Q ≤ Real.log 6 + 2 * Real.log ((r : ℝ) + t) := by
    have h6 : Q ≤ 6 * ((r : ℝ) + t) ^ 2 := by rw [hQ]; nlinarith
    calc Real.log Q ≤ Real.log (6 * ((r : ℝ) + t) ^ 2) := Real.log_le_log (by linarith) h6
      _ = Real.log 6 + 2 * Real.log ((r : ℝ) + t) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  calc (r : ℝ) * Real.log q / ((q : ℝ) - 1) ≤ 2 * r * (Real.log q / q) := s1.trans s2.le
    _ ≤ 2 * r * (Real.log Q / Q) := mul_le_mul_of_nonneg_left hant (by positivity)
    _ ≤ 2 * Real.log Q := s3
    _ ≤ 2 * Real.log 6 + 4 * Real.log ((r : ℝ) + t) := by linarith

theorem sq_le_dim (f r m : ℕ) (hf : 2 ≤ f) (hr : 2 ≤ r) (hm : 2 ≤ m) : r ^ 2 ≤ m * (f * r.choose 2) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  have h : (s + 2).choose 2 * 2 = (s + 2) * (s + 1) := by
    have := Nat.add_one_mul_choose_eq (s + 1) 1
    rw [Nat.choose_one_right] at this
    exact this.symm
  have h4 : 2 * (2 * (s + 2).choose 2) ≤ m * (f * (s + 2).choose 2) :=
    Nat.mul_le_mul hm (Nat.mul_le_mul hf le_rfl)
  nlinarith

variable {D : D7} {L : SizeData₂ D}

theorem one_le_L (s : Scale) : 1 ≤ s.L := Real.one_le_rpow s.one_lt_alt.le s.eps_pos.le

theorem ranks_le {P : ParameterChoice' D L} (T : ParamsT D L P) :
    1 ≤ T.PP ∧ (D.R.f : ℝ) * D.R.r ≤ L.sc.b ∧ (D.R.r : ℝ) + D.R.t ≤ 2 * L.sc.b := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hL := one_le_L L.sc
  have hfr : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hf hr
  have hZ : (D.R.f : ℝ) * D.R.r ≤ zBase L := le_mul_of_one_le_right (by positivity) hL
  have hZ1 : 1 ≤ zBase L := hfr.trans hZ
  have hZP : zBase L ≤ T.PP := by
    rw [T.PP_eq]
    have a : zBase L ≤ zBase L ^ T.eP := Real.self_le_rpow_of_one_le hZ1 (by linarith [T.eP_ge])
    exact a.trans (le_mul_of_one_le_left (by linarith) T.one_le_CP)
  have hPP : 1 ≤ T.PP := hZ1.trans hZP
  have hTO : (1 : ℝ) ≤ T.TO := by exact_mod_cast (by have := T.TO_40; omega : 1 ≤ T.TO)
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (by linarith)
  have hs : (T.TO : ℝ) * T.PP ≤ L.sc.b := T.TO_PP'.trans (Real.rpow_le_self_of_one_le hb (by norm_num))
  have hP2 : T.PP ≤ (T.TO : ℝ) * T.PP := le_mul_of_one_le_left (by linarith) hTO
  refine ⟨hPP, by linarith, ?_⟩
  have e1 : (D.R.r : ℝ) + D.R.t = T.nP + T.TO * T.nWn := by exact_mod_cast T.split
  have e2 : (T.nP : ℝ) ≤ T.nWn := by exact_mod_cast T.nW_lo.2.2
  have e3 : (T.TO : ℝ) * T.nWn ≤ T.TO * T.PP := mul_le_mul_of_nonneg_left T.nW_le (by linarith)
  linarith [T.nW_le]

variable {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem unitE_eq : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := rfl

theorem dim_eq : GlobalTheory.CompHt.dimFlag (dat p i) = D.R.f * D.R.r.choose 2 := by
  exact GlobalTheory.SlopeRec.dimFlag_eq p.fw.laws.pins ⟨Nat.le_add_left 1 i, i.2⟩

theorem lenT_mul_le {P : ParameterChoice' D L} (T : ParamsT D L P) :
    (lenT p i T.PP : ℝ) * (D.R.r : ℝ) ^ 3 ≤ 2 * L.sc.b := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hr2 : 2 ≤ D.R.r := by unfold Ranks.r; omega
  have hsq := sq_le_dim D.R.f D.R.r D.R.m (by unfold Ranks.f; omega) hr2 h1
  rw [← T.Dp_eq] at hsq
  have hD1 : 1 ≤ T.Dp := by
    rcases Nat.eq_zero_or_pos T.Dp with h | h
    · rw [h] at hsq; nlinarith
    · exact h
  have hsq' : (D.R.r : ℝ) ^ 2 ≤ D.R.m * T.Dp := by exact_mod_cast hsq
  have hD : (1 : ℝ) ≤ T.Dp := by exact_mod_cast hD1
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hPP := (ranks_le T).1
  have hW : (1 : ℝ) ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hPP) (one_le_pow₀ hD)) hk
  have hlen : (lenT p i T.PP : ℝ) ≤ 2 * (T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k) := by
    unfold lenT
    rw [dim_eq, ← T.Dp_eq]
    have a := (Nat.ceil_lt_add_one (a := T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k / D.R.m) (by positivity)).le
    have b : T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k / D.R.m ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k := div_le_self (by linarith) hm
    linarith
  have hr3 : (D.R.r : ℝ) ^ 3 ≤ D.R.r * (D.R.m * T.Dp) := by
    rw [pow_succ']; exact mul_le_mul_of_nonneg_left hsq' (by positivity)
  have hb : (D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3 ≤ L.sc.b := by
    refine le_trans ?_ T.b_ge
    have : T.CbN * (D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3 =
      T.CbN * ((D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3) := by ring
    rw [this]
    exact le_mul_of_one_le_left (by positivity) T.CbN_ge
  calc (lenT p i T.PP : ℝ) * (D.R.r : ℝ) ^ 3
      ≤ 2 * (T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k) * (D.R.r * (D.R.m * T.Dp)) :=
        mul_le_mul hlen hr3 (by positivity) (by linarith)
    _ = 2 * ((D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3) := by ring
    _ ≤ 2 * L.sc.b := by linarith

theorem numAt {P : ParameterChoice' D L} (T : ParamsT D L P) (hll : 1 ≤ Real.log (Real.log L.sc.x)) :
    NumAt p i T.PP (|L.Ct| + 20) := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have h3 := D.R.rank_add_five_le
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hL := one_le_L L.sc
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (by linarith)
  have hlb : Real.log L.sc.b = L.sc.L := Real.log_exp _
  have hC := abs_nonneg L.Ct
  obtain ⟨-, hfr, hrt⟩ := ranks_le T
  have hCL : 20 * L.sc.L ≤ (|L.Ct| + 20) * L.sc.L := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hlr : Real.log D.R.r ≤ L.sc.L :=
    hlb ▸ Real.log_le_log (by linarith) ((le_mul_of_one_le_left (by linarith) hf).trans hfr)
  have hlf : Real.log D.R.f ≤ L.sc.L :=
    hlb ▸ Real.log_le_log (by linarith) ((le_mul_of_one_le_right (by linarith) hr).trans hfr)
  refine ⟨hL, hb, by linarith, hll, ?_, ?_, by linarith, ?_, ?_, ?_⟩
  · rw [unitE_eq]
    refine le_mul_of_one_le_left ?_ (by linarith)
    have : 0 ≤ L.sc.L := by linarith
    have : 0 ≤ Real.log (Real.log L.sc.x) := by linarith
    positivity
  · have hx := L.sc.one_lt_alt
    have hlx : 0 < Real.log L.sc.x := Real.log_pos hx
    have hk : (2 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 2 ≤ D.R.k)
    have hkt : (D.R.k : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.k ≤ D.R.t)
    have a : Real.log D.R.k ≤ L.Ct * Real.log L.sc.x := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log (by linarith) (hkt.trans L.t_win.2)
    have b : Real.log D.R.k ≤ (|L.Ct| + 1) * Real.log L.sc.x :=
      a.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self L.Ct]) hlx.le)
    have c := Real.log_le_log (Real.log_pos (by linarith)) b
    rw [Real.log_mul (by linarith) hlx.ne'] at c
    have d := Real.log_le_sub_one_of_pos (by linarith : 0 < |L.Ct| + 1)
    nlinarith
  · have hQ : (D.host.QS : ℝ) ≤ (D.R.f : ℝ) ^ 2 := by
      have := D.host.QS_le
      exact_mod_cast this.trans (Nat.pow_le_pow_left (by unfold Ranks.f; omega) 2)
    have hQ0 : (0 : ℝ) < D.host.QS := by exact_mod_cast D.host.QS_pos
    have a := Real.log_le_log hQ0 hQ
    rw [Real.log_pow] at a
    push_cast at a
    have h2' := Real.log_two_gt_d9
    unfold Formalism.MainNotions.DIV.Cons.vd2
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  · exact (lenT_mul_le p i T).trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  · intro q hq
    have hq' : 4 * D.R.t * D.R.r + 1 < q := by
      rcases Finset.mem_insert.1 hq with h | h
      · exact h ▸ D.host.qd_big.1
      · exact (Finset.mem_singleton.1 h) ▸ D.host.qd_big.2
    have a := r_log_div_le D.R.r D.R.t q hr1 (by omega) hq'
    have b : Real.log ((D.R.r : ℝ) + D.R.t) ≤ Real.log 2 + L.sc.L := by
      rw [← hlb, ← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by positivity) hrt
    have c := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
    have d := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have e : (|L.Ct| + 20) * L.sc.L ≤ (|L.Ct| + 20) * D.R.m * L.sc.L :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by linarith) hm) (by linarith)
    linarith

theorem numPt : NumPt := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨|Fm.Ct| + 20, by positivity,
    Real.exp (Real.exp 1), fun x hx hle ι p _ i _ => ?_⟩⟩⟩
  rw [← Fm.Ct_eq x ι]
  refine numAt p i (Fm.parT x hx ι) ?_
  rw [Fm.L_x x ι hx, Real.le_log_iff_exp_le, Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le hle)]
  · exact hle
  · exact Real.log_pos ((Real.one_lt_exp_iff.2 (Real.exp_pos 1)).trans_le hle)

theorem numPt_of_size : Size → NumPt := fun _ => numPt

end GlobalTheory.RefSum.NumSizes

end
