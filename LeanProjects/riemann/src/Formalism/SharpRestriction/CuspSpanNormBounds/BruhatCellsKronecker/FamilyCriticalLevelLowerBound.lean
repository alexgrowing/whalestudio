import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VandermondeRatioHarmonic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CriticalThresholdLowerBound
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

theorem v_ge_of_hyp {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ}
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : 1 ≤ D.host.v := by
  dsimp only [StandingHypotheses] at hH
  exact hH.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ka_pos_of {D : D7} (hv : 1 ≤ D.host.v) : 0 < D.host.ka := by
  show 0 < Real.pi / D.host.v
  exact div_pos Real.pi_pos (by linarith)

theorem gg_pos (D : D7) : 0 < gg D := by
  unfold gg
  exact mul_pos (Nat.cast_pos.mpr (D.host.g_prime 0).pos) (Nat.cast_pos.mpr (D.host.g_prime 1).pos)

theorem VV_pos (D : D7) (τ : D.what₂.Tau) : 0 < VV D τ := by
  unfold VV
  exact mul_pos (D.dsig_pos τ) (Finset.prod_pos fun i _ => by positivity)

theorem last_shifted_parameter_eq {D : D7} {C0 : ℝ} (hD : StandingNumericalData D C0) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    ¬ IsTop D τ → uOne D u τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2 := by
  dsimp only [StandingNumericalData] at hD
  exact hD.2.2.2.2.1 u τ

theorem critical_level_ratio_le_exp {D : D7} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT C1 : ℝ} (h40 : 40 ≤ Cl)
    (hC1 : Real.exp (3 / 4) ≤ C1) : LocalBesselAndTopKernel.SecondBoundHyp D large₂ C0 C' Cl Cg cb Cu cT CT C1 := by
  rintro ⟨hD, hH, -⟩ u u' τ
  have ok := cfg_ok hD hH τ
  have sm := cfg_small hH h40 τ
  have hka := ka_pos_of (v_ge_of_hyp hH)
  have hrd : 0 < D.host.rdE := Formalism.MainNotions.S.rdE_pos D
  have hTW := Formalism.FourierDecayAlt.P.critical_threshold_words (cfgOf D τ) (deOf D u) (deOf D u') D.host.ka D.host.rdE
    (gg D) (VV D τ) ok sm.hvth (isWord_deOf D u) (isWord_deOf D u') hka hrd (gg_pos D) (VV_pos D τ)
  rw [← Tcrit_eq D u τ hka.le, ← Tcrit_eq D u' τ hka.le, ← Vand_u D u τ (last_shifted_parameter_eq hD u τ),
    ← Vand_u D u' τ (last_shifted_parameter_eq hD u' τ)]
  exact le_trans (le_of_eq hTW.1) (hTW.2.2.trans hC1)

theorem cfg_aeff (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : (cfgOf D τ).aeff = aEff D u τ := by
  simp only [aEff, uOne_one D u τ]
  by_cases h : S.IsTop D τ
  · simp [cfgOf, Sz.Cfg.aeff, h]
  · have hk : 1 ≤ D.R.k - 1 := by
      have := D.R.m_add_three_le_k
      omega
    have hv := cfg_v D τ 1 le_rfl hk
    simp [cfgOf, Sz.Cfg.aeff, h] at hv ⊢
    first | exact hv | linarith | simp [hv]

theorem cfg_aeff_pos {D : D7} {τ : D.what₂.Tau} (ok : (cfgOf D τ).Ok) : 0 < (cfgOf D τ).aeff := by
  generalize cfgOf D τ = c at ok ⊢
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast ok.hk
  have hD := ok.hDel
  have hv0 := ok.hv0
  have hv1 : 0 ≤ c.v 1 := by
    unfold Sz.Cfg.v
    push_cast
    nlinarith
  have ha := ok.ha
  unfold Sz.Cfg.aeff
  split_ifs with ht
  · obtain ⟨hbp, -⟩ := ok.htop ht
    have hb1 := ok.hb1
    exact div_pos (mul_pos (by nlinarith) (by linarith)) (mul_pos (by linarith) (by linarith))
  · nlinarith

theorem cOne_ge {c : Sz.Cfg} {bb : ℝ} (ok : c.Ok) (sm : c.Small bb) : 1 / 5 ≤ Sz.cOne c bb := by
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast ok.hk
  have hm : (2 : ℝ) ≤ c.m := by exact_mod_cast ok.hm
  have hD := ok.hDel
  have hE : 9 / 10 ≤ Real.exp (-(2 * c.m * Real.log bb / c.k)) := by
    have h := Real.add_one_le_exp (-(2 * c.m * Real.log bb / c.k))
    linarith [sm.hmu]
  have hV : 0 ≤ c.vthp ∧ c.vthp ≤ 1 / 10 := by
    unfold Sz.Cfg.vthp
    split_ifs with ht
    · obtain ⟨hbp, -⟩ := ok.htop ht
      have hb1 := ok.hb1
      have hvth := sm.hvth
      unfold Sz.Cfg.vth at hvth
      have hbp0 : 0 < c.bp := by linarith
      rw [div_le_iff₀ (by linarith)] at hvth
      constructor
      · positivity
      · rw [div_le_iff₀ hbp0]
        nlinarith [mul_nonneg (sub_nonneg.mpr hm) (mul_nonneg (by linarith : (0 : ℝ) ≤ c.k)
          (by linarith : (0 : ℝ) ≤ c.Del))]
    · norm_num
  unfold Sz.cOne
  rw [le_div_iff₀ (by linarith [hV.1])]
  norm_num
  linarith [hV.1, hV.2, hE]

theorem critical_level_lower_bound {D : D7} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT ep0 CV C3' : ℝ} (h40 : 40 ≤ Cl)
    (hep : ep0 ≤ 1 / 2) (hC3 : 1 ≤ C3') : LocalBesselAndTopKernel.LocalTiedPairs D large₂ C0 C' Cl Cg cb Cu cT CT ep0 CV C3' := by
  rintro ⟨hD, hH, -⟩ hG u τ
  have ok := cfg_ok hD hH τ
  have sm := cfg_small hH h40 τ
  have hv1 := v_ge_of_hyp hH
  have hka := ka_pos_of hv1
  have hH' := hH
  dsimp only [StandingHypotheses] at hH'
  obtain ⟨-, -, hmf, hfk, -, -, -, -, -, -, -, hg1, -, -, -, hbO, -, -, -, -, -, -, -, -, -⟩ := hH'
  have hm2 : 2 ≤ D.R.m := ok.hm
  have hk16n : 16 ≤ D.R.k :=
    le_trans (le_trans (by norm_num) (Nat.pow_le_pow_left hm2 4)) (hmf.trans hfk)
  have hk16 : (16 : ℝ) ≤ D.R.k := by exact_mod_cast hk16n
  have hb1 : 1 ≤ large₂.sc.b := sm.hbb
  have hrd1 : 1 ≤ D.host.rdE := by
    have hvdef : D.host.v = D.host.rdE / 2 := rfl
    linarith
  have hka_eq : D.host.ka = 2 * Real.pi / D.host.rdE := by
    show Real.pi / D.host.v = _
    rw [show D.host.v = D.host.rdE / 2 from rfl]
    field_simp
  have hg0 : (16 : ℝ) ^ 8 ≤ (D.host.g 0 : ℝ) := by
    have h16 : (16 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
    exact le_trans (pow_le_pow_left₀ (by norm_num) h16 8) hg1
  have hg1' : (1 : ℝ) ≤ (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).one_lt.le
  have hgg : 2 * Real.pi ≤ gg D := by
    unfold gg
    nlinarith [Real.pi_le_four]
  obtain ⟨hG1, hG2⟩ := hG τ
  have hVVpos := VV_pos D τ
  have hvpos : 0 < vand (lamSH D.R (D.hc τ)) := by
    by_contra hneg
    push_neg at hneg
    have h3 : Real.exp (CV * D.R.k * D.R.m * large₂.sc.L) * vand (lamSH D.R (D.hc τ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hneg
    linarith
  have hFD : Sz.FormalDegreeLower (cfgOf D τ) (1 / 2) (VV D τ) := by
    unfold Sz.FormalDegreeLower
    rw [Vand_lam D τ]
    nlinarith
  have hTL := Formalism.FourierDecayAlt.P.critical_threshold_lower_bound (cfgOf D τ) D.R.rS large₂.sc.b (deOf D u) D.host.ka D.host.rdE
    (gg D) (VV D τ) ok (m_eq D) sm (isWord_deOf D u) hrd1 hka_eq hgg hFD
  rw [← Tcrit_eq D u τ hka.le, ← Vand_u D u τ (last_shifted_parameter_eq hD u τ), ← cfg_aeff D u τ]
  refine le_trans ?_ hTL
  show _ ≤ Sz.cOne (cfgOf D τ) large₂.sc.b * gg D ^ D.R.m * (D.host.ka ^ (D.R.m - 1))⁻¹ *
    (∏ j ∈ Finset.Icc 1 D.R.m, bOne D τ j) / (cfgOf D τ).aeff
  have hpow : D.host.ka ^ (-((D.R.m : ℝ) - 1)) = (D.host.ka ^ (D.R.m - 1))⁻¹ := by
    rw [Real.rpow_neg hka.le, show ((D.R.m : ℝ) - 1) = ((D.R.m - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega : 1 ≤ D.R.m)]
      simp, Real.rpow_natCast]
  rw [hpow]
  have hkC : (D.R.k : ℝ) ^ (-C3') ≤ 1 / 5 := by
    have h1 : (D.R.k : ℝ) ^ (-C3') ≤ (D.R.k : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_neg_one] at h1
    have h2 : (D.R.k : ℝ)⁻¹ ≤ (16 : ℝ)⁻¹ := (inv_le_inv₀ (by linarith) (by norm_num)).2 hk16
    linarith
  have hc1 := cOne_ge ok sm
  have hP : 0 ≤ ∏ j ∈ Finset.Icc 1 D.R.m, bOne D τ j := by
    refine Finset.prod_nonneg fun j hj => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    exact le_trans (le_max_of_le_left (Real.rpow_nonneg (by linarith) _)) (hbO τ j h1 h2).1
  have hA : 0 ≤ gg D ^ D.R.m * (D.host.ka ^ (D.R.m - 1))⁻¹ * (∏ j ∈ Finset.Icc 1 D.R.m, bOne D τ j)
      / (cfgOf D τ).aeff := by
    have h1 := cfg_aeff_pos ok
    have h2 := gg_pos D
    positivity
  have key := mul_le_mul_of_nonneg_right (hkC.trans hc1) hA
  exact (le_of_eq (by ring)).trans (key.trans (le_of_eq (by ring)))

variable {eps : ℝ}

theorem family_critical_level_ratio (Fm : FamP eps) {C0 Cg cb Cu cT CT C1 : ℝ} (h40 : 40 ≤ sCl Fm)
    (hC1 : Real.exp (3 / 4) ≤ C1) : LocalBesselAndTopKernel.TheoremThreePassage Fm C0 Cg cb Cu cT CT C1 :=
    ⟨0, fun x _ i hh => critical_level_ratio_le_exp h40 hC1 hh⟩

theorem family_critical_level_lower_bound (Fm : FamP eps) {C0 Cg cb Cu cT CT ep0 CV C3' : ℝ} (h40 : 40 ≤ sCl Fm)
    (hep : ep0 ≤ 1 / 2) (hC3 : 1 ≤ C3') (hg : LocalBesselAndTopKernel.FamilyTopBound Fm C0 Cg cb Cu cT CT ep0 CV) :
    LocalBesselAndTopKernel.LocalSplitExponents Fm C0 Cg cb Cu cT CT C3' := by
  obtain ⟨x0, hx0⟩ := hg
  refine ⟨x0, fun x hx i hh => ?_⟩
  exact critical_level_lower_bound (C0 := C0) (CV := CV) (ep0 := ep0) h40 hep hC3 hh (hx0 x hx i hh)

end Formalism.MainNotions.BridgeLemma

end
