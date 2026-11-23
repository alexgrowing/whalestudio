import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsOneD
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNDn

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem corank_one_numeric_ineq {f r k : ℕ} {b pe cr c C δ C0 Γ Ex Yc Yt rD EC eH : ℝ} (hb : 2 ≤ b) (hf : 1 ≤ f) (hc : 0 ≤ c)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) (hC0 : 1 ≤ C0) (hΓ : 0 ≤ Γ) (hEx : 0 ≤ Ex) (hrD : 0 ≤ rD) (hY0 : 0 ≤ Yc) (hY : Yc ≤ Yt)
    (h2 : 2 * Real.sqrt (2 * C0) * c ≤ C) (hΓE : Γ * Ex ≤ EC)
    (hexp : 1 + 12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + pe * (2 * (2 * cr) + 2 * cr + 6 * ((r : ℝ) + 1) ^ 2) ≤ eH) :
    2 * ((c ^ f * (((b ^ pe) ^ cr) ^ 2 * ((b ^ pe) ^ cr) ^ 2 * ((b ^ pe) ^ cr) ^ 2) * Γ * Ex * ((1 + δ) * rD) *
        Real.sqrt (2 * C0 * Γ ^ 2 * (Yc ^ f) ^ k)) * ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2) ≤
      (C ^ f * b ^ eH * Γ * EC * Real.sqrt (Yt ^ (k * f))) * rD := by
  have hb0 : 0 < b := by linarith
  have hP0 : 0 < b ^ pe := Real.rpow_pos_of_pos hb0 _
  have hQ := rows_num_Q (f := f) (r := r) (pe := pe) (E1 := 2 * cr) (cr := cr) hb hδ0 hδ
  have e1 : ((b ^ pe) ^ (2 * cr)) ^ 2 = ((b ^ pe) ^ cr) ^ 2 * ((b ^ pe) ^ cr) ^ 2 := by
    rw [show 2 * cr = cr + cr by ring, Real.rpow_add hP0]; ring
  rw [e1] at hQ
  have hQ2 := hQ.trans (Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ b) hexp)
  have hs : Real.sqrt (2 * C0 * Γ ^ 2 * (Yc ^ f) ^ k) = Real.sqrt (2 * C0) * Γ * Real.sqrt ((Yc ^ f) ^ k) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hΓ]
  have hW : Real.sqrt ((Yc ^ f) ^ k) ≤ Real.sqrt (Yt ^ (k * f)) := by
    apply Real.sqrt_le_sqrt
    rw [← pow_mul, mul_comm f k]
    exact pow_le_pow_left₀ hY0 hY _
  set K : ℝ := 2 * Real.sqrt (2 * C0) with hK
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ Real.sqrt (2 * C0) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    rw [hK]; linarith
  have hKc : K * c ^ f ≤ C ^ f := by
    calc K * c ^ f ≤ K ^ f * c ^ f := by
          apply mul_le_mul_of_nonneg_right (le_self_pow₀ hK1 (by omega)) (by positivity)
      _ = (K * c) ^ f := (mul_pow K c f).symm
      _ ≤ C ^ f := pow_le_pow_left₀ (by positivity) h2 _
  rw [hs]
  calc 2 * ((c ^ f * (((b ^ pe) ^ cr) ^ 2 * ((b ^ pe) ^ cr) ^ 2 * ((b ^ pe) ^ cr) ^ 2) * Γ * Ex * ((1 + δ) * rD) *
        (Real.sqrt (2 * C0) * Γ * Real.sqrt ((Yc ^ f) ^ k))) * ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2)
      = (K * c ^ f) * ((1 + δ) * (((b ^ pe) ^ cr) ^ 2 * ((b ^ pe) ^ cr) ^ 2 * ((b ^ pe) ^ cr) ^ 2) *
          ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2) * Γ * (Γ * Ex) * Real.sqrt ((Yc ^ f) ^ k) * rD := by
        rw [hK]; ring
    _ ≤ C ^ f * b ^ eH * Γ * EC * Real.sqrt (Yt ^ (k * f)) * rD := by
        have hEC : 0 ≤ EC := le_trans (by positivity) hΓE
        have hC : 0 ≤ C := le_trans (by positivity) h2
        gcongr

theorem corank_one_exponent_ineq {m f r c mx C : ℝ} (hm : m = 2 * r + 2) (hr : 0 ≤ r) (hf : 1 ≤ f) (hc : 0 ≤ c) (hmx : 0 ≤ mx)
    (hC : 4 + 2 * (c ^ 2 + 2 * mx) * (c + 1) ≤ C ^ 2) :
    1 + 12 * f * (r + 1) ^ 2 + (c ^ 2 * m ^ 3 * f + 4 * (mx * m ^ 2 * f * (r + 1))) *
        (2 * (2 * (c * r ^ 2)) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2) ≤ C * m ^ 2 * f * (C * m ^ 3) := by
  have hm2 : 2 ≤ m := by linarith
  have hr1 : r + 1 = m / 2 := by linarith
  set p : ℝ := c ^ 2 + 2 * mx with hp
  have hp0 : 0 ≤ p := by positivity
  have e1 : c ^ 2 * m ^ 3 * f + 4 * (mx * m ^ 2 * f * (r + 1)) = m ^ 3 * f * p := by rw [hr1, hp]; ring
  have hrm : r ^ 2 ≤ m ^ 2 / 4 := by
    have : r ≤ m / 2 := by linarith
    nlinarith
  have b1 : 2 * (2 * (c * r ^ 2)) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2 ≤ 2 * (c + 1) * m ^ 2 := by
    rw [hr1]
    have : c * r ^ 2 ≤ c * (m ^ 2 / 4) := mul_le_mul_of_nonneg_left hrm hc
    have hm0 : 0 ≤ m ^ 2 := by positivity
    nlinarith
  have m25 : m ^ 2 ≤ m ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have m5 : 1 ≤ m ^ 5 := one_le_pow₀ (by linarith)
  have fm5 : 1 ≤ f * m ^ 5 := by nlinarith
  have hfm : 0 ≤ m ^ 3 * f * p := by positivity
  calc 1 + 12 * f * (r + 1) ^ 2 + (c ^ 2 * m ^ 3 * f + 4 * (mx * m ^ 2 * f * (r + 1))) *
        (2 * (2 * (c * r ^ 2)) + 2 * (c * r ^ 2) + 6 * (r + 1) ^ 2)
      ≤ 1 + 3 * f * m ^ 2 + m ^ 3 * f * p * (2 * (c + 1) * m ^ 2) := by
        rw [e1]
        have : 12 * f * (r + 1) ^ 2 = 3 * f * m ^ 2 := by rw [hr1]; ring
        rw [this]
        have := mul_le_mul_of_nonneg_left b1 hfm
        linarith
    _ ≤ f * m ^ 5 + 3 * (f * m ^ 5) + (2 * p * (c + 1)) * (f * m ^ 5) := by
        have : f * m ^ 2 ≤ f * m ^ 5 := mul_le_mul_of_nonneg_left m25 (by linarith)
        have e : m ^ 3 * f * p * (2 * (c + 1) * m ^ 2) = (2 * p * (c + 1)) * (f * m ^ 5) := by ring
        rw [e]; linarith
    _ = (4 + 2 * p * (c + 1)) * (f * m ^ 5) := by ring
    _ ≤ C ^ 2 * (f * m ^ 5) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = C * m ^ 2 * f * (C * m ^ 3) := by ring

section End

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

variable {C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm C : ℝ} {q : ℕ}

theorem weightRatio_le (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A) (h1 : 4 * Real.sqrt A ≤ C) :
    wordPairWeightRatio D u u' ≤ C * (gg D)⁻¹ ^ (2 * D.R.rS + 1) * ((D.R.k : ℝ) ^ D.R.rS)⁻¹ := by
  have hg : 0 < gg D := by linarith [two_le_gg_of_count_hypotheses hH.1]
  have hTT : Tr D u' / Tr D u ≤ A := hH.2.2.1
  have e : (gS D : ℝ) * gg D ^ (-(D.R.m : ℝ)) = (gg D)⁻¹ ^ (2 * D.R.rS + 1) := by
    rw [← rows_gg_eq, Real.rpow_neg hg.le, Real.rpow_natCast, d_m_eq D, inv_pow, pow_succ (gg D) (2 * D.R.rS + 1)]
    field_simp
  unfold wordPairWeightRatio
  rw [mul_assoc (4 * Real.sqrt (Tr D u' / Tr D u)), e]
  have h3 : 4 * Real.sqrt (Tr D u' / Tr D u) ≤ C := le_trans (by gcongr) h1
  gcongr

theorem corankOneBound_le (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A) (hc : 0 ≤ c) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (h1 : 4 * Real.sqrt A ≤ C) (h2 : 2 * Real.sqrt (2 * C0) * c ≤ C) (h3 : large₂.CGam + C2 ≤ C)
    (hexp : 1 + 12 * (D.R.f : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2 + pairCountExponentShift D c Ch *
        (2 * (2 * (c * (D.R.rS : ℝ) ^ 2)) + 2 * (c * (D.R.rS : ℝ) ^ 2) + 6 * ((D.R.rS : ℝ) + 1) ^ 2) ≤
      C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 * D.R.f * (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3)) :
    corankOneBound D large₂ u u' c C2 Ch δ C0 ≤ oneB D large₂ C * rDD D u' := by
  have hb2 := d_two_le_b D large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  have hg : 0 ≤ gg D := by linarith [two_le_gg_of_count_hypotheses hH.1]
  have hΓ : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  have hL : 0 ≤ large₂.sc.L := by linarith [d_one_le_L D large₂]
  have hm : (D.R.m : ℝ) = ((2 * D.R.rS + 2 : ℕ) : ℝ) := by rw [d_m_eq D]
  have hm1 : (1 : ℝ) ≤ D.R.m := by rw [rows_m_cast]; have : (0 : ℝ) ≤ D.R.rS := by positivity
                                   linarith
  have hΓE : GamS D large₂ * logHeightExp D large₂ C2 ≤
      Real.exp (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) := by
    unfold GamS logHeightExp
    rw [← Real.exp_add, d_log_b, ← hm]
    apply Real.exp_le_exp.2
    have hfL : 0 ≤ (D.R.f : ℝ) * large₂.sc.L := by positivity
    have h56 : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 6 := pow_le_pow_right₀ hm1 (by norm_num)
    have hG := large₂.CGam_pos
    have a1 : large₂.CGam * (D.R.m : ℝ) ^ 5 + C2 * (D.R.m : ℝ) ^ 6 ≤ C * (D.R.m : ℝ) ^ 6 := by
      have : large₂.CGam * (D.R.m : ℝ) ^ 5 ≤ large₂.CGam * (D.R.m : ℝ) ^ 6 := mul_le_mul_of_nonneg_left h56 hG.le
      have h6 : 0 ≤ (D.R.m : ℝ) ^ 6 := by positivity
      nlinarith
    calc large₂.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L + C2 * (D.R.m : ℝ) ^ 6 * D.R.f * large₂.sc.L
        = (large₂.CGam * (D.R.m : ℝ) ^ 5 + C2 * (D.R.m : ℝ) ^ 6) * ((D.R.f : ℝ) * large₂.sc.L) := by ring
      _ ≤ (C * (D.R.m : ℝ) ^ 6) * ((D.R.f : ℝ) * large₂.sc.L) := mul_le_mul_of_nonneg_right a1 hfL
      _ = _ := by ring
  have key := corank_one_numeric_ineq (f := D.R.f) (r := D.R.rS) (k := D.R.k) (pe := pairCountExponentShift D c Ch) (cr := c * (D.R.rS : ℝ) ^ 2)
    (rD := rDD D u') hb2 (rows_f_pos D) hc hδ0 hδ hH.1.2.2 hΓ.le (by unfold logHeightExp; exact (Real.exp_pos _).le)
    (rows_rDD_nonneg D u') (weightRatio_nonneg D hg u u') (weightRatio_le hH h1) h2 hΓE hexp
  rw [Real.rpow_mul hb0.le] at key
  unfold corankOneBound labelPairConstant smallTermBound rows_Phi rows_P oneB LatticeSumBounds.bigH
  exact key

theorem corank_one_bound_general (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q)
    (hSW : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (hC4 : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c)
    (hF : rowsSingleFibre X Y) (hF' : wordPairTermSingleFibre X Y) (h7 : VanishingOnXAndXPlus.adm7 D large₂ C' Cl Cg cb Cu cT CT C0)
    (hδ2 : δ ≤ 1 / 2) (hδm0 : 0 ≤ δm) (hδm : δm ≤ 1 / 4) (hCa : 0 ≤ Ca) (hCak : (max Ca 1) ^ 3 ≤ D.R.k)
    (hq1 : 12 * (c * (D.R.rS : ℝ) ^ 2) + C2 * (D.R.m : ℝ) ^ 2 / 2 + |C2 * (D.R.m : ℝ) ^ 4| +
      12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1))
    (h1 : 4 * Real.sqrt A ≤ C) (h2 : 2 * Real.sqrt (2 * C0) * c ≤ C) (h3 : large₂.CGam + C2 ≤ C)
    (hexp : 1 + 12 * (D.R.f : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2 + pairCountExponentShift D c Ch *
        (2 * (2 * (c * (D.R.rS : ℝ) ^ 2)) + 2 * (c * (D.R.rS : ℝ) ^ 2) + 6 * ((D.R.rS : ℝ) + 1) ^ 2) ≤
      C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 * D.R.f * (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3)) : RowsOne X Y C :=
  rows_RowBound_mono Y (corank_one_bound_of_fibres Y h hSW hC4 hF hF' h7 hδ2 hδm0 hδm hCa hCak hq1)
    (corankOneBound_le h.hH h.hc h.hδ (by linarith) h1 h2 h3 hexp) h.hdim.le

theorem corank_one_bound_of_fibres_alt (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q)
    (hSW : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (hC4 : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c)
    (hF : rowsSingleFibre X Y) (hF' : wordPairTermSingleFibre X Y) (h7 : VanishingOnXAndXPlus.adm7 D large₂ C' Cl Cg cb Cu cT CT C0)
    (hδ2 : δ ≤ 1 / 2) (hδm0 : 0 ≤ δm) (hδm : δm ≤ 1 / 4) (hCa : 0 ≤ Ca) (hCak : (max Ca 1) ^ 3 ≤ D.R.k)
    (hq1 : 12 * (c * (D.R.rS : ℝ) ^ 2) + C2 * (D.R.m : ℝ) ^ 2 / 2 + |C2 * (D.R.m : ℝ) ^ 4| +
      12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1))
    (h1 : 4 * Real.sqrt A ≤ C) (h2 : 2 * Real.sqrt (2 * C0) * c ≤ C) (h3 : large₂.CGam + C2 ≤ C)
    (hC : 4 + 2 * (c ^ 2 + 2 * max (Ch - c) 0) * (c + 1) ≤ C ^ 2) : RowsOne X Y C := by
  refine corank_one_bound_general Y h hSW hC4 hF hF' h7 hδ2 hδm0 hδm hCa hCak hq1 h1 h2 h3 ?_
  have hm : (D.R.m : ℝ) = ((2 * D.R.rS + 2 : ℕ) : ℝ) := by rw [d_m_eq D]
  rw [← hm]
  unfold pairCountExponentShift
  exact corank_one_exponent_ineq (rows_m_cast D) (by positivity) (by exact_mod_cast rows_f_pos D) h.hc (le_max_right _ _) hC

theorem corank_one_bound_of_fibres_ge_one (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q)
    (hSW : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (hC4 : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c)
    (hF : rowsSingleFibre X Y) (hF' : wordPairTermSingleFibre X Y) (h7 : VanishingOnXAndXPlus.adm7 D large₂ C' Cl Cg cb Cu cT CT C0)
    (hδ2 : δ ≤ 1 / 2) (hδm0 : 0 ≤ δm) (hδm : δm ≤ 1 / 4) (hCa1 : 1 ≤ Ca) (hCak1 : Ca ^ 3 ≤ D.R.k)
    (hq1 : 12 * (c * (D.R.rS : ℝ) ^ 2) + C2 * (D.R.m : ℝ) ^ 2 / 2 + |C2 * (D.R.m : ℝ) ^ 4| +
      12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1))
    (h1 : 4 * Real.sqrt A ≤ C) (h2 : 2 * Real.sqrt (2 * C0) * c ≤ C) (h3 : large₂.CGam + C2 ≤ C)
    (hC : 4 + 2 * (c ^ 2 + 2 * max (Ch - c) 0) * (c + 1) ≤ C ^ 2) : RowsOne X Y C :=
  corank_one_bound_of_fibres_alt Y h hSW hC4 hF hF' h7 hδ2 hδm0 hδm (by linarith) (by rw [max_eq_left hCa1]; exact hCak1) hq1 h1 h2 h3 hC

theorem corank_one_bound_of_injective_terms (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q)
    (hSW : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (hC4 : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c)
    (hTI : wordPairTermInjective X Y) (hBL : wordPairBetaLattice D u u') (h7 : VanishingOnXAndXPlus.adm7 D large₂ C' Cl Cg cb Cu cT CT C0)
    (hδ2 : δ ≤ 1 / 2) (hδm0 : 0 ≤ δm) (hδm : δm ≤ 1 / 4) (hCa : 0 ≤ Ca) (hCak : (max Ca 1) ^ 3 ≤ D.R.k)
    (hq1 : 12 * (c * (D.R.rS : ℝ) ^ 2) + C2 * (D.R.m : ℝ) ^ 2 / 2 + |C2 * (D.R.m : ℝ) ^ 4| +
      12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1))
    (h1 : 4 * Real.sqrt A ≤ C) (h2 : 2 * Real.sqrt (2 * C0) * c ≤ C) (h3 : large₂.CGam + C2 ≤ C)
    (hC : 4 + 2 * (c ^ 2 + 2 * max (Ch - c) 0) * (c + 1) ≤ C ^ 2) : RowsOne X Y C :=
  corank_one_bound_of_fibres_alt Y h hSW hC4 (rows_OneFibre_of Y hTI (rows_BetaUnique_of Y hBL))
    (rows_OneFibre'_of' Y hTI (rows_BetaUnique_of Y hBL)) h7 hδ2 hδm0 hδm hCa hCak hq1 h1 h2 h3 hC

end End

end Formalism.MainNotions.BridgeLemma₂

end
