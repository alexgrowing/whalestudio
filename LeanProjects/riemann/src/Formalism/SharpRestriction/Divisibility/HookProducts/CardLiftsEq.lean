import Formalism.SharpRestriction.Divisibility.SlopeExcess.ConstRankBaseLePolyFourth
import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds
import Formalism.SharpRestriction.GrowthBounds.JointsLit
import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NotSingularOfCentral
import Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers.FirstTermSizeBound
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.Row4

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.MainNotions.WeightDegreeSizes

variable {D : D7} {L : SizeData₂ D}

def gB (L : SizeData₂ D) (p : ℕ) : ℝ :=
  if (p : ℝ) ≤ L.sc.X'' D.R.n then (D.R.m : ℝ) * (4 * (D.host.TT.card : ℝ) * L.sc.a / (p : ℝ)) else 0

theorem gB_nonneg (L : SizeData₂ D) (p : ℕ) : 0 ≤ gB L p := by
  have hx : 0 ≤ L.sc.x := le_of_lt (lt_trans zero_lt_one L.sc.one_lt_alt)
  have ha : 0 ≤ L.sc.a := by
    simp only [Scale.a, Scale.b]
    exact mul_nonneg hx (Real.exp_pos _).le
  unfold gB
  split_ifs
  · have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
    have hT : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
    have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
    exact mul_nonneg hm (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hT) ha) hp)
  · exact le_refl 0

theorem card_lifts_eq (D : D7) : ((SizeData₂.lifts D).card : ℝ) = D.R.m := by
  simp [SizeData₂.lifts]

theorem logWeight_nonneg (w : D.what₂.places.Pl) : 0 ≤ SizeData₂.lwP w := by
  simp only [SizeData₂.lwP, lw]
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

theorem gainD_sum_le (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (hK : K.Nonneg)
    (hF : ∀ w, ParametersFill X K w) (w : D.what₂.places.Pl) :
    ∑ j ∈ SizeData₂.lifts D, L.gainD j w ≤ gB L (D.what₂.places.resChar w) := by
  have hp := D.what₂.places.resChar_prime w
  have ha := Formalism.MainNotions.DIV.Proofs.HHParts.a_nonneg L
  unfold gB
  split_ifs with hX
  · have hS : ∀ j ∈ SizeData₂.lifts D, L.gainD j w ≤ 4 * (D.host.TT.card : ℝ) * L.sc.a / (D.what₂.places.resChar w : ℝ) := by
      intro j hj
      have hR : 0 ≤ 4 * (D.host.TT.card : ℝ) * L.sc.a / (D.what₂.places.resChar w : ℝ) := by positivity
      unfold SizeData₂.gainD
      split_ifs
      · exact hR
      by_cases hs : w ∈ L.supp
      swap
      · rw [L.gain_supp j w hs]; exact hR
      by_cases hin : IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)
      swap
      · rw [(L.not_inert w (fun h => hin (Or.inr h)) (fun h => hin (Or.inl h))).1 j]; exact hR
      rw [(hF w).2.2.2.1 hs hin j hj]
      exact (Formalism.MainNotions.AuxBlock8.Pf.gain_bounds P X K hK _ _ (Formalism.MainNotions.AuxBlock8.Pf.inWin_sizeData L) _ hp j hj).2
    refine le_trans (Finset.sum_le_sum hS) ?_
    rw [Finset.sum_const, nsmul_eq_mul, card_lifts_eq]
  · have hz : ∀ j ∈ SizeData₂.lifts D, L.gainD j w = 0 := by
      intro j hj
      unfold SizeData₂.gainD
      split_ifs
      · rfl
      · exact gain_above X K hF j hj w (not_le.mp hX)
    rw [Finset.sum_eq_zero hz]

theorem ga_le_at (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (hK : K.Nonneg)
    (hF : ∀ w, ParametersFill X K w) (hM : Formalism.MainNotions.CornerGLContinuity.MertensBound D) :
    L.Ga ≤ 16 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a * Real.log (L.sc.X'' D.R.n + 1) := by
  classical
  have ha := Formalism.MainNotions.DIV.Proofs.HHParts.a_nonneg L
  set B : ℝ := 4 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a with hBdef
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  have hX0 : 0 ≤ L.sc.X'' D.R.n := by
    unfold Scale.X''
    exact div_nonneg ha Formalism.MainNotions.DIV.Proofs.HHParts.w''_nonneg
  have s1 : L.Ga ≤ 2 * ∑ w ∈ L.supp, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * gB L (D.what₂.places.resChar w) := by
    unfold SizeData₂.Ga
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    unfold SizeData₂.sz
    have ht : 0 ≤ L.tau w := by
      rw [(hF w).2.2.2.2.1]
      exact Formalism.MainNotions.G.TopChoiceBounds.tauP_nonneg X K _ _ _
    have hg := gainD_sum_le P X K hK hF w
    have hc : 0 ≤ 2 * SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) :=
      mul_nonneg (mul_nonneg zero_le_two (logWeight_nonneg w)) (Nat.cast_nonneg _)
    calc 2 * SizeData₂.lwP w * ((D.what₂.places.ramIdx w : ℝ) * ((∑ j ∈ SizeData₂.lifts D, L.gainD j w) - L.tau w))
        = (2 * SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) * ((∑ j ∈ SizeData₂.lifts D, L.gainD j w) - L.tau w) := by ring
      _ ≤ (2 * SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) * gB L (D.what₂.places.resChar w) :=
          mul_le_mul_of_nonneg_left (by linarith) hc
      _ = 2 * (SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * gB L (D.what₂.places.resChar w)) := by ring
  have s2 := Formalism.MainNotions.G.TopChoiceBounds.bt_sum_by_prime L.supp (gB L) (gB_nonneg L)
  set P' : Finset ℕ := (Finset.range ⌈L.sc.X'' D.R.n + 1⌉₊).filter Nat.Prime with hP'
  have hf0 : ∀ p : ℕ, 0 ≤ B * (Real.log p / p) := fun p =>
    mul_nonneg hB (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  have hpt : ∀ p ∈ L.supp.image D.what₂.places.resChar,
      Real.log (p : ℝ) * gB L p ≤ if p ∈ P' then B * (Real.log p / p) else 0 := by
    intro p hp
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.1 hp
    have hpr := D.what₂.places.resChar_prime w
    unfold gB
    split_ifs with h1 h2 h2
    · rw [hBdef]
      have hp0 : (D.what₂.places.resChar w : ℝ) ≠ 0 := by exact_mod_cast hpr.ne_zero
      apply le_of_eq
      field_simp
    · exfalso
      apply h2
      rw [hP', Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_ceil.2 (by linarith), hpr⟩
    · rw [mul_zero]; exact hf0 _
    · rw [mul_zero]
  have s3 : ∑ p ∈ L.supp.image D.what₂.places.resChar, Real.log (p : ℝ) * gB L p ≤ ∑ p ∈ P', B * (Real.log p / p) := by
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [Finset.sum_ite_mem]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun p _ _ => hf0 p)
  have s4 : ∑ p ∈ P', B * (Real.log p / p) ≤ B * (2 * Real.log (L.sc.X'' D.R.n + 1)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hM _ (by linarith)) hB
  have e : 16 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a * Real.log (L.sc.X'' D.R.n + 1) =
      2 * (B * (2 * Real.log (L.sc.X'' D.R.n + 1))) := by rw [hBdef]; ring
  rw [e]
  linarith

open Formalism.MainNotions.DIV.Proofs.HHParts in

theorem logX_le (hN : SizeN L) (hK : SizeK L) :
    Real.log (L.sc.X'' D.R.n + 1) ≤ 4 * Formalism.MainNotions.DIV.Proofs.szPol L := by
  obtain ⟨hn1, hn2⟩ := hN
  obtain ⟨hk1, -⟩ := hK
  have hx1 := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have hx0 : 0 < L.sc.x := lt_trans zero_lt_one hx1
  have hnpos : 0 < (D.R.n : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hn1
  have hX'1 : 1 ≤ L.sc.X' := by
    simp only [Scale.X']
    exact Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hX'0 : 0 < L.sc.X' := lt_of_lt_of_le zero_lt_one hX'1
  have ha : 0 < L.sc.a := by
    simp only [Scale.a, Scale.b]
    exact mul_pos hx0 (Real.exp_pos _)
  have hXeq : L.sc.X'' D.R.n = L.sc.x * D.R.n * L.sc.X' := by
    simp only [Scale.X'', Scale.w'', Scale.b']
    field_simp [ha.ne', hX'0.ne', hx0.ne', hnpos.ne']
    try ring
  have hbound : L.sc.X'' D.R.n + 1 ≤ (L.sc.x + 1) * ((D.R.n : ℝ) + 1) * L.sc.X' := by
    rw [hXeq]
    nlinarith [mul_nonneg (add_nonneg (add_nonneg hx0.le hnpos.le) zero_le_one) (sub_nonneg.mpr hX'1)]
  have hpos : 0 < L.sc.X'' D.R.n + 1 := by
    rw [hXeq]
    have := mul_pos (mul_pos hx0 hnpos) hX'0
    linarith
  have hx1' : (0 : ℝ) < L.sc.x + 1 := by linarith
  have hn1' : (0 : ℝ) < (D.R.n : ℝ) + 1 := by linarith
  have hlog : Real.log (L.sc.X'' D.R.n + 1) ≤
      Real.log (L.sc.x + 1) + Real.log ((D.R.n : ℝ) + 1) + L.sc.x ^ (L.sc.eps / 3) := by
    calc Real.log (L.sc.X'' D.R.n + 1)
        ≤ Real.log ((L.sc.x + 1) * ((D.R.n : ℝ) + 1) * L.sc.X') := Real.log_le_log hpos hbound
      _ = Real.log (L.sc.x + 1) + Real.log ((D.R.n : ℝ) + 1) + L.sc.x ^ (L.sc.eps / 3) := by
        rw [Real.log_mul (mul_pos hx1' hn1').ne' hX'0.ne', Real.log_mul hx1'.ne' hn1'.ne']
        simp only [Scale.X', Real.log_exp]
  have h1 : Real.log (L.sc.x + 1) ≤ L.sc.x := by
    linarith [Real.log_le_sub_one_of_pos hx1']
  have h2 : Real.log ((D.R.n : ℝ) + 1) ≤ D.R.n := by
    linarith [Real.log_le_sub_one_of_pos hn1']
  have h3 : L.sc.x ^ (L.sc.eps / 3) ≤ L.sc.x ^ L.sc.eps :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have h4 : L.sc.x ≤ D.R.k := by
    have h41 : L.sc.x ^ (1 : ℝ) ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - Formalism.MainNotions.szTh L) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by simp only [Formalism.MainNotions.szTh]; linarith)
    rw [Real.rpow_one] at h41
    linarith
  have h5 : (D.R.n : ℝ) ≤ D.R.k := by
    have h51 : L.sc.x ^ (2 + 8 * L.sc.eps + Formalism.MainNotions.szTh L) ≤
        L.sc.x ^ (9 / 2 + 10 * L.sc.eps - Formalism.MainNotions.szTh L) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by simp only [Formalism.MainNotions.szTh]; linarith)
    linarith
  have hL0 : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hx0.le _
  have hLeq : L.sc.L = L.sc.x ^ L.sc.eps := rfl
  unfold Formalism.MainNotions.DIV.Proofs.szPol
  rw [hLeq]
  have hf : (0 : ℝ) ≤ (D.R.f : ℝ) := by positivity
  have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := by positivity
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := by positivity
  have hNm : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by positivity
  linarith

open Formalism.MainNotions.DIV.Proofs.HHParts in

theorem ga_le_pol (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (hK : K.Nonneg)
    (hF : ∀ w, ParametersFill X K w) (hM : Formalism.MainNotions.CornerGLContinuity.MertensBound D) (hS : SizesAt L) :
    L.Ga ≤ 64 * Formalism.MainNotions.DIV.Proofs.szPol L ^ 4 * L.sc.b := by
  have hga := ga_le_at P X K hK hF hM
  have hlog := logX_le hS.1 hS.2.2.1
  have hN' : SizeN L := hS.1
  have hK' : SizeK L := hS.2.2.1
  have hTTs : Formalism.MainNotions.SizeTT L := hS.2.2.2.2.2.2.2.1
  obtain ⟨-, hn2⟩ := hN'
  obtain ⟨hk1, -⟩ := hK'
  obtain ⟨-, hTT⟩ := hTTs
  have hx1 := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have hx0 : 0 < L.sc.x := lt_trans zero_lt_one hx1
  have hb : 0 < L.sc.b := by
    simp only [Scale.b]
    exact Real.exp_pos _
  have hδ : L.sc.delta1 ≤ 1 := by
    simp only [Scale.delta1]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
  have hn0 : (0 : ℝ) ≤ (D.R.n : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  have hTT' : (D.host.TT.card : ℝ) ≤ 2 * D.R.n := by
    simp only [Formalism.MainNotions.szNst] at hTT
    have q := mul_le_mul_of_nonneg_left hδ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hn0)
    linarith
  have hnx : (D.R.n : ℝ) * L.sc.x ≤ D.R.k := by
    have q1 : L.sc.x ^ (2 + 8 * L.sc.eps + Formalism.MainNotions.szTh L) * L.sc.x =
        L.sc.x ^ (2 + 8 * L.sc.eps + Formalism.MainNotions.szTh L + 1) := (Real.rpow_add_one hx0.ne' _).symm
    have q2 : L.sc.x ^ (2 + 8 * L.sc.eps + Formalism.MainNotions.szTh L + 1) ≤
        L.sc.x ^ (9 / 2 + 10 * L.sc.eps - Formalism.MainNotions.szTh L) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by simp only [Formalism.MainNotions.szTh]; linarith)
    have q3 := mul_le_mul_of_nonneg_right hn2 hx0.le
    linarith
  have hL0 : 0 ≤ L.sc.L := by
    simp only [Scale.L]
    exact Real.rpow_nonneg hx0.le _
  have hf : (0 : ℝ) ≤ (D.R.f : ℝ) := by positivity
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := by positivity
  have hNm : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by positivity
  have hmk : (D.R.m : ℝ) + D.R.k ≤ Formalism.MainNotions.DIV.Proofs.szPol L := by
    unfold Formalism.MainNotions.DIV.Proofs.szPol; linarith
  have hQ1 : 1 ≤ Formalism.MainNotions.DIV.Proofs.szPol L := by
    unfold Formalism.MainNotions.DIV.Proofs.szPol; linarith
  have hQ0 : 0 ≤ Formalism.MainNotions.DIV.Proofs.szPol L := by linarith
  have e1 : (D.host.TT.card : ℝ) * L.sc.x ≤ 2 * D.R.k := by
    have q := mul_le_mul_of_nonneg_right hTT' hx0.le
    linarith
  have e2 : (D.R.m : ℝ) * ((D.host.TT.card : ℝ) * L.sc.x) ≤ (D.R.m : ℝ) * (2 * D.R.k) :=
    mul_le_mul_of_nonneg_left e1 hm0
  have e3 : ((D.R.m : ℝ) + D.R.k) * ((D.R.m : ℝ) + D.R.k) ≤
      Formalism.MainNotions.DIV.Proofs.szPol L * Formalism.MainNotions.DIV.Proofs.szPol L :=
    mul_self_le_mul_self (by linarith) hmk
  have hA : (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x ≤ Formalism.MainNotions.DIV.Proofs.szPol L ^ 2 := by
    linarith [sq_nonneg ((D.R.m : ℝ) - D.R.k), mul_self_nonneg (Formalism.MainNotions.DIV.Proofs.szPol L)]
  have hA0 : 0 ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x :=
    mul_nonneg (mul_nonneg hm0 hT0) hx0.le
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  rw [ha] at hga
  have s1 : L.Ga ≤ 16 * L.sc.b * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x) *
      Real.log (L.sc.X'' D.R.n + 1) := by linarith
  have s2 : 16 * L.sc.b * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x) *
      Real.log (L.sc.X'' D.R.n + 1) ≤
      16 * L.sc.b * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x) *
      (4 * Formalism.MainNotions.DIV.Proofs.szPol L) :=
    mul_le_mul_of_nonneg_left hlog (mul_nonneg (mul_nonneg (by norm_num) hb.le) hA0)
  have s3 : 16 * L.sc.b * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x) *
      (4 * Formalism.MainNotions.DIV.Proofs.szPol L) ≤
      16 * L.sc.b * Formalism.MainNotions.DIV.Proofs.szPol L ^ 2 * (4 * Formalism.MainNotions.DIV.Proofs.szPol L) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (mul_nonneg (by norm_num) hb.le)) (by linarith)
  have s4 : Formalism.MainNotions.DIV.Proofs.szPol L ^ 3 ≤ Formalism.MainNotions.DIV.Proofs.szPol L ^ 4 :=
    pow_le_pow_right₀ hQ1 (by norm_num)
  have s5 : 64 * Formalism.MainNotions.DIV.Proofs.szPol L ^ 3 * L.sc.b ≤ 64 * Formalism.MainNotions.DIV.Proofs.szPol L ^ 4 * L.sc.b :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left s4 (by norm_num)) hb.le
  linarith [s1, s2, s3, s5]

theorem ga_pow {eps : ℝ} (Fm : FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
      (Fm.L x i).Ga ≤ x ^ (4 * (max Fm.Ct 5 + 3) + 1) * (Fm.L x i).sc.b := by
  refine ⟨64, fun x hx hx1 i => ?_⟩
  have h := ga_le_pol (Fm.params x hx1 i) (Fm.Gx x i) Fm.GK Fm.GK_nonneg (fun w => Fm.fills x hx1 i w)
    (Formalism.MainNotions.G.Joints.Lit.mertens_bound _) (Fm.sizes x hx1 i)
  have hX : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hCt : (Fm.L x i).Ct = Fm.Ct := Fm.Ct_eq x i
  have hb := Formalism.MainNotions.DIV.Proofs.bPol_le (Fm.sizes x hx1 i) 64 4 (by rw [hX]; norm_num; linarith)
  rw [hX, hCt] at hb
  have e : ((4 : ℕ) : ℝ) * (max Fm.Ct 5 + 3) + 1 = 4 * (max Fm.Ct 5 + 3) + 1 := by norm_num
  rw [e] at hb
  exact h.trans hb

end Formalism.MainNotions.DIV.HookProducts.Row4

end
