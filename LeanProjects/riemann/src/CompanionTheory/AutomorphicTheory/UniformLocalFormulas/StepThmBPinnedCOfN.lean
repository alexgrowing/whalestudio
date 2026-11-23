import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThmBChainG

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.BDat Formalism.L2.SG.ThmBUseR
  Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BDatR Formalism.L2.SG.Pf.GoodS Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.MainStatements.RowRest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev AN {X : HidaSetting D} {θ : ℝ} {C : Choice X θ} (hB : WuBessel C) (u u' : D.what₂.Word) (dg : D.what₂.Tau → ℝ) :
    ∀ τ, LocS (WX C u u' τ) := fun τ => { locS hB u u' τ with deg := dg τ }

theorem goodW_all {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    GoodW D τ u u' θ (WX C u u' τ) :=
  goodW_of C u u' τ (colsTypeTr C u τ) (colsTypeTr C u' τ) (zTr C u τ) (zTr C u' τ) (haarTr C τ)

theorem goodS_deg {X : HidaSetting D} {θ : ℝ} {C : Choice X θ} (hLF : LocFactor C) (hB : WuBessel C) (u u' : D.what₂.Word)
    (τ : D.what₂.Tau) : ∃ d : ℝ, GoodS D (lamD D τ) (AN hB u u' (fun _ => d) τ) := by
  have hsm := WuDec.lowSmoothSK (dsTr C τ) (isLowUnitH_base_vector C τ)
  have hLu := l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u τ
  have hLu' := l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u' τ
  set v := vOf X τ
  have hd : (0 : ℝ) < Module.finrank ℂ (X.Vloc u v) := by exact_mod_cast finrank_pos u v
  have hd' : (0 : ℝ) < Module.finrank ℂ (X.Vloc u' v) := by exact_mod_cast finrank_pos u' v
  have hL : 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal := ENNReal.toReal_pos hLu.1 hLu.2.ne
  have hL' : 0 < (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal := ENNReal.toReal_pos hLu'.1 hLu'.2.ne
  have hc : 0 < cOf hB u τ := div_pos hL hd
  obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
  have hε : ∀ i, epsSH D.R i = X.B.I.ε v (Fin.cast (Choice.n_eq' X).symm i) := fun i => by
    rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl)
  have hF := Choice.fdegHpk_tr (Choice.n_eq' X) (X.B.I.ε v) (epsSH D.R) hε (X.B.σ v) (X.ds v).2.2.1
    (Formalism.L2.SG.Pf.RowDictPf.fdeg_of_schur X Formalism.L2.SG.Pf.RowDictPf.schur_orthogonality_discrete_series v)
    (C.Q τ) (C.Qi τ) (C.isT τ).2.1 (C.isT τ).2.2.1 P hP
  have hF2 := Formalism.L2.SG.Pf.RowDictPf.isFdeg_smul (D.s.cdScale_pos _ (epsSH D.R)) hF
  refine ⟨_, Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ, Formalism.L2.SG.Pf.dsTr C τ, (hB u τ).choose_spec.1,
    isBesselMapSm_smul _ (hB u' τ).choose_spec.1, hsm, v0_ne C τ, C.y_low τ, hc, ?_, ?_, P, hP.1, hF2⟩
  · show l2SG (C.nuS u τ) (phiOf hB u τ) = ENNReal.ofReal (cOf hB u τ * Module.finrank ℂ (X.Vloc u v))
    rw [Formalism.L2.SG.LocWSOf.cOf, div_mul_cancel₀ _ hd.ne', ENNReal.ofReal_toReal hLu.2.ne]
  · show l2SG (C.nuS u' τ) (fun m => sclOf hB u u' τ • phiOf hB u' τ m) =
      ENNReal.ofReal (cOf hB u τ * Module.finrank ℂ (X.Vloc u' v))
    rw [l2SG_const_smul, sclOf]
    set a := cOf hB u τ * (Module.finrank ℂ (X.Vloc u' v) : ℝ) / (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal
      with ha
    have ha0 : 0 ≤ a := div_nonneg (mul_nonneg hc.le hd'.le) hL'.le
    have hnorm : (‖((Real.sqrt a : ℝ) : ℂ)‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal a := by
      rw [← enorm_eq_nnnorm, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt ha0]
    rw [hnorm, ← ENNReal.ofReal_toReal hLu'.2.ne, ← ENNReal.ofReal_mul ha0, ha, div_mul_cancel₀ _ hL'.ne']

theorem ties_coreN {τ₀ Rw I₀ H H₁ : Type} [Fintype I₀] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (XT : Formalism.FourierDecayAlt.PB.Terms τ₀ Rw I₀ H H₁)
    {Cl' Nu : Type} (N : Formalism.FourierDecayAlt.PN.NGData τ₀ D.host.E D.R.rS Cl' Nu)
    {large₂ : SizeData₂ D} {X : HidaSetting D} (u u' : D.what₂.Word)
    {C' Cl Cg cb Cw cT CT C0 C1 Ca Ch Cs Cβ Cb Cn Ire : ℝ} (A : ℕ)
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0) (hTT : HypTT D u u') (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (hAmp : Formalism.MainNotions.S.Bridge.AmpIsBessel D large₂ C' Cl Cg cb Cw cT CT C0 0 C1 Ca)
    (hStd : Formalism.MainNotions.S.Bridge.StdOfHyp D large₂ C' Cl Cg cb Cw cT CT C0 Ch Cs Cs Cβ)
    (hTF : Formalism.MainNotions.TFrameOfHyp D large₂ C' Cl Cg cb Cw cT CT C0)
    (hpt : Formalism.L2.SG.ThmBUse.PtTie XT N (D.mem u).A.T (D.mem u').A.T)
    (hwt : Formalism.L2.SG.ThmBUse.WtTie XT N (D.mem u).A.T (D.mem u').A.T A 1)
    (hIre : 0 ≤ Ire) {θ : ℝ} (Cc : Choice X θ) (hBs : WuBessel Cc) (hθ0 : 0 < θ) (hθw : normWin D large₂ C1 θ)
    (dg : D.what₂.Tau → ℝ) (hAg : ∀ τ, GoodS D (lamD D τ) (AN hBs u u' dg τ))
    {Cfac : ℝ} (hCfac : 0 ≤ Cfac)
    (hJF : JointAmplitudeFactorizationRotated XT N large₂ C1 (WX Cc u u') (AX hBs u u') (D.mem u).A.T (D.mem u').A.T Cfac)
    (hNF : ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
        (∀ τ, IsSection D.R.k D.R.rS (WX Cc u u' τ).z (WX Cc u u' τ).z' (sec τ)) →
        ENNReal.ofReal Cfac * ∏ τ, MMv D u u' (AX hBs u u' τ) (sec τ) ≤
          ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire))
    (hCs : 0 ≤ Cs) (hka : 0 < Formalism.MainNotions.S.Bridge.kaS D) (hβ : 0 ≤ Cβ) :
    TiesR XT N Ch Cs (D.mem u).A.T (D.mem u').A.T (large₂.sc.b ^ Cβ) A Cb
      (Real.exp ((max 0 Cb * Cβ + |Ca| + |Cn|) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f * Real.log large₂.sc.b) * Ire) := by
  have hWg : ∀ τ, GoodW D τ u u' θ (WX Cc u u' τ) := fun τ =>
    goodW_all Cc u u' τ
  have hv : 0 < D.host.v := by
    unfold Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
    have h : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
      abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
    have := Real.rpow_pos_of_pos h ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))
    linarith
  have hS := hStd hH
  have hF := hTF hH
  let I : AmpIn large₂ C1 Ca u u' θ hT hT' := ampInOf hAmp hH hTT hθw hT hT' (WX Cc u u') (AN hBs u u' dg) hWg hAg
  have hok : ∀ τ, LocOk D Ch Cs (I.L τ) (lamSH D.R (D.hc τ)) (kaRe D) (large₂.sc.b ^ Cβ) (kaRe D) := fun τ =>
    locOk_locB D τ u u' θ (WX Cc u u' τ) (AN hBs u u' dg τ) (hWg τ) (hAg τ) hT hT' hka hv hθ0 (hS τ u u').1 (hF u) (hF u')
  have hCj : 0 ≤ Cfac * ∏ τ, (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) :=
    mul_nonneg hCfac (Finset.prod_nonneg fun τ _ => mul_nonneg (I.hK τ).le
      (Real.rpow_nonneg (by unfold Scale.b; positivity) _))
  exact ⟨bdOf I.toInputs hok, 1, _, zero_le_one, hCj,
    gaps_bdOf I.toInputs hok (fun τ => (hS τ u u').2) hCs le_rfl, hpt, hwt,
    jointAmplitude_bound_rotated XT N I hok hka hCfac hJF,
    normTie_bdOf I hok hCfac hIre hβ (hNF I.sec I.sec_spec)⟩

def RowDataN (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ (θ : ℝ) (C : Choice X θ) (hB : WuBessel C), 0 < θ ∧ normWin D large₂ C1 θ ∧
    (∃ dg : D.what₂.Tau → ℝ, ∀ τ, GoodS D (lamD D τ) (AN hB u u' dg τ)) ∧
    JointAmplitudePoints.RMeasExP u u' C ∧ JointAmplitudePoints.LocalAmplitudesPositive Y u u' ν C hB ∧ JointAmplitudePoints.ThetaWinP Y u u' ν C hB large₂ C1 ∧
    ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
      (∀ τ, IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
      ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤ ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)

def RowDataUnifN : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 Cn : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν → RowDataN large₂ Y u u' ν C1 Cn Ire

theorem rowDataUnifN_of_6 (hBW : BesselOfW) (hR : ThmBChain6.AmplitudeBoundsAllChoicesUniform) : RowDataUnifN := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, Cn, a, b, h2⟩ := hR Cg cb Cw cT CT C0
  refine ⟨C1, Cn, max a 29, max b 16, fun C' Cl h1 h3 D large₂ X Y u u' hc hb X0 ψ hBT sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hO ν hp => ?_⟩
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D :=
    Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hc.1.1 (le_trans (le_max_right _ _) h3) (le_trans (le_max_right _ _) h1)
  obtain ⟨hIre, θ, hθ, hw, hrest⟩ := h2 C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h3) D large₂ X Y u u'
    hc hb X0 ψ hBT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hO ν hp
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨Cc⟩ := choiceExists X θ hθ
  have hLF := LocF.locFactor_holds hG Cc
  have hB : WuBessel Cc := wuBesselOfLoc_all Cc hG hBW hLF (fun τ => dsTr Cc τ) (fun τ => haarTr Cc τ)
    (fun u τ => colsTypeTr Cc u τ)
  obtain ⟨⟨νl, hQ, hU⟩, hK, hWK, hN⟩ := hrest Cc hB
  have hJ := OOCore3.jFactPK_of_core Y u u' ν Cc hB large₂ C1 (OOCore3.ooCorePK_of Y u u' ν Cc hB large₂ C1 νl hQ
    (LocNorm.locNormPK_of Y u u' Cc hB large₂ C1 νl hU (fun w τ => LocJEq.integrand_aesm Cc hB u u' τ _ _) hK hWK))
  choose dg hdg using goodS_deg hLF hB u u'
  exact ⟨hIre, θ, Cc, hB, hθ, hw, ⟨dg, hdg⟩, RMeasP.rMeasExP_of_goodW Cc u u' (goodW_all Cc u u'),
    OOCore3.localAmplitudesPositive_of_kernel Y u u' ν Cc hB large₂ C1 hJ, OOCore3.thetaWinP_of_K Y u u' ν Cc hB large₂ C1 hJ, hN⟩

theorem stepThmBPinnedC_ofN (hB : JointNormBoundRotatedUniform) (hA : AmpUnif) (hP : PtUnif)
    (hR : RowDataUnifN) : StepThmBPinnedC := by
  intro Cg cb Cw cT CT C0 A
  obtain ⟨C1, Cn, c₀, d₀, hR2⟩ := hR Cg cb Cw cT CT C0
  obtain ⟨Ca, -, a₀, b₀, hA2⟩ := hA Cg cb Cw cT CT C0 C1
  obtain ⟨g₀, h₀, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨Cb, Cg₀, hB1⟩ := hB (A : ℝ) (|CT| + 1 / 8 + 2 * |Cg|) (Nat.cast_nonneg A)
  have hCB : 0 ≤ max 0 Cb * max 2 Cw + |Ca| + |Cn| := by
    have h1 : 0 ≤ max 0 Cb := le_max_left _ _
    have h2 : 0 ≤ max 2 Cw := le_trans (by norm_num) (le_max_left _ _)
    have := mul_nonneg h1 h2
    positivity
  refine ⟨max 0 Cb * max 2 Cw + |Ca| + |Cn|, hCB, max a₀ (max c₀ g₀),
    max 8 (max (128 * max Cg₀ 0) (max b₀ (max d₀ h₀))), ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u u' hctx hb X0 ψ hBT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBO ν hpin νL ng
  have hC'a : a₀ ≤ C' := le_trans (le_max_left _ _) hC'
  have hC'c : c₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC'
  have hC'g : g₀ ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC'
  have hCl8 : 8 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCls : 128 * max Cg₀ 0 ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hClb : b₀ ≤ Cl :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hCl
  have hCld : d₀ ≤ Cl := le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) (le_max_right _ _)) hCl
  have hClh : h₀ ≤ Cl := le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) (le_max_right _ _)) hCl
  have hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 := hctx.1
  have hTT := hypTT_of hctx.2.1
  obtain ⟨hT, hT'⟩ := tr_pos hctx.2.1
  have hm := cl_le_m hH
  have hs0 : 0 ≤ max Cg₀ 0 := le_max_right _ _
  have hmR : (128 : ℝ) * |max Cg₀ 0| ≤ D.R.m := by rw [abs_of_nonneg hs0]; linarith
  have hmR' : |max Cg₀ 0| ≤ D.R.m := by rw [abs_of_nonneg hs0]; linarith
  have hβ2 : (2 : ℝ) ≤ max 2 Cw := le_max_left _ _
  have hCh0 : (0 : ℝ) ≤ |CT| + 1 / 8 + 2 * |Cg| := by positivity
  have hChT : CT ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by
    have h1 : |CT| + 1 / 8 + 2 * |Cg| ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by nlinarith
    have h2 : CT ≤ |CT| + 1 / 8 + 2 * |Cg| := by have := le_abs_self CT; have := abs_nonneg Cg; linarith
    linarith
  have hChg : 1 / 8 + 2 * Cg ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by
    have h1 : |CT| + 1 / 8 + 2 * |Cg| ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by nlinarith
    have h2 : 1 / 8 + 2 * Cg ≤ |CT| + 1 / 8 + 2 * |Cg| := by have := le_abs_self Cg; have := abs_nonneg CT; linarith
    linarith
  have hStd := Formalism.MainNotions.BridgeLemma.stdOfHyp_rec D large₂ C' Cl Cg cb Cw cT CT C0 (|CT| + 1 / 8 + 2 * |Cg|) (max Cg₀ 0)
    (max Cg₀ 0) (max 2 Cw) hCl8 hCh0 hβ2 (le_max_right _ _) hChT hChg hmR hmR'
  have hka := (Formalism.MainNotions.BridgeLemma.std_kaS hH hCl8).1
  obtain ⟨hIre, θ, Cc, hBs, hθ0, hθw, ⟨dg, hAg⟩, hM, hPp, hTh, hNF⟩ :=
    hR2 C' Cl hC'c hCld D large₂ X Y u u' hctx hb X0 ψ hBT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBO ν hpin
  have hTB : 0 ≤ Real.exp ((max 0 Cb * max 2 Cw + |Ca| + |Cn|) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f *
      Real.log large₂.sc.b) * Ire := mul_nonneg (Real.exp_pos _).le hIre
  exact pointSum_of_B3R (Y.tO u u') (NOf2 Y u u' νL ν ng) (hB1 (max Cg₀ 0) (le_max_left _ _) D)
    (fun γ => Formalism.L2.SG.ThmBUse.J2of_nonneg' Y u u' ν γ) hTB
    (ties_coreN (Y.tO u u') (NOf2 Y u u' νL ν ng) u u' A hH hTT hT hT' (hA2 C' Cl hC'a hClb D large₂) hStd
      (fun _ => hctx.2.2.2.2.2.2.2.2.2) (point_amplitude_relation_normalized Y u u' (hP2 C' Cl hC'g hClh D large₂ X Y u u' hctx) νL ν ng)
      (Formalism.L2.SG.ThmBUse.weight_normalized Formalism.L2.SG.Pf.weightConclusion Y u u' νL ν ng A) hIre Cc hBs hθ0 hθw dg hAg zero_le_one
      (jointAmplitudeFactorizationRotated_of Y u u' large₂ C1 Cc hBs ν νL ng (RelPtR.relPtExPR_holds Cc u u') hM hPp hTh)
      (fun sec hs => by rw [ENNReal.ofReal_one, one_mul]; exact hNF sec hs) hs0 hka (by linarith))

theorem stepThmBG_ofN (hB : JointNormBoundRotatedUniform) (hA : AmpUnif) (hP : PtUnifG)
    (hR : RowDataUnifN) : StepThmBG := by
  intro Cg cb Cw cT CT C0 A
  obtain ⟨C1, Cn, c₀, d₀, hR2⟩ := hR Cg cb Cw cT CT C0
  obtain ⟨Ca, -, a₀, b₀, hA2⟩ := hA Cg cb Cw cT CT C0 C1
  obtain ⟨g₀, h₀, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨Cb, Cg₀, hB1⟩ := hB (A : ℝ) (|CT| + 1 / 8 + 2 * |Cg|) (Nat.cast_nonneg A)
  have hCB : 0 ≤ max 0 Cb * max 2 Cw + |Ca| + |Cn| := by
    have h1 : 0 ≤ max 0 Cb := le_max_left _ _
    have h2 : 0 ≤ max 2 Cw := le_trans (by norm_num) (le_max_left _ _)
    have := mul_nonneg h1 h2
    positivity
  refine ⟨max 0 Cb * max 2 Cw + |Ca| + |Cn|, hCB, max a₀ (max c₀ g₀),
    max 8 (max (128 * max Cg₀ 0) (max b₀ (max d₀ h₀))), ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hctx hb X0 ψ hBT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBO ν hpin νL ng
  have hC'a : a₀ ≤ C' := le_trans (le_max_left _ _) hC'
  have hC'c : c₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC'
  have hC'g : g₀ ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC'
  have hCl8 : 8 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCls : 128 * max Cg₀ 0 ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hClb : b₀ ≤ Cl :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hCl
  have hCld : d₀ ≤ Cl := le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) (le_max_right _ _)) hCl
  have hClh : h₀ ≤ Cl := le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) (le_max_right _ _)) hCl
  have hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 := hctx.1
  have hTT := hypTT_of hctx.2.1
  obtain ⟨hT, -⟩ := tr_pos hctx.2.1
  have hm := cl_le_m hH
  have hs0 : 0 ≤ max Cg₀ 0 := le_max_right _ _
  have hmR : (128 : ℝ) * |max Cg₀ 0| ≤ D.R.m := by rw [abs_of_nonneg hs0]; linarith
  have hmR' : |max Cg₀ 0| ≤ D.R.m := by rw [abs_of_nonneg hs0]; linarith
  have hβ2 : (2 : ℝ) ≤ max 2 Cw := le_max_left _ _
  have hCh0 : (0 : ℝ) ≤ |CT| + 1 / 8 + 2 * |Cg| := by positivity
  have hChT : CT ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by
    have h1 : |CT| + 1 / 8 + 2 * |Cg| ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by nlinarith
    have h2 : CT ≤ |CT| + 1 / 8 + 2 * |Cg| := by have := le_abs_self CT; have := abs_nonneg Cg; linarith
    linarith
  have hChg : 1 / 8 + 2 * Cg ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by
    have h1 : |CT| + 1 / 8 + 2 * |Cg| ≤ max 2 Cw * (|CT| + 1 / 8 + 2 * |Cg|) := by nlinarith
    have h2 : 1 / 8 + 2 * Cg ≤ |CT| + 1 / 8 + 2 * |Cg| := by have := le_abs_self Cg; have := abs_nonneg CT; linarith
    linarith
  have hStd := Formalism.MainNotions.BridgeLemma.stdOfHyp_rec D large₂ C' Cl Cg cb Cw cT CT C0 (|CT| + 1 / 8 + 2 * |Cg|) (max Cg₀ 0)
    (max Cg₀ 0) (max 2 Cw) hCl8 hCh0 hβ2 (le_max_right _ _) hChT hChg hmR hmR'
  have hka := (Formalism.MainNotions.BridgeLemma.std_kaS hH hCl8).1
  obtain ⟨hIre, θ, Cc, hBs, hθ0, hθw, ⟨dg, hAg⟩, hM, hPp, hTh, hNF⟩ :=
    hR2 C' Cl hC'c hCld D large₂ X Y u u hctx hb X0 ψ hBT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBO ν hpin
  have hTB : 0 ≤ Real.exp ((max 0 Cb * max 2 Cw + |Ca| + |Cn|) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f *
      Real.log large₂.sc.b) * Ire := mul_nonneg (Real.exp_pos _).le hIre
  exact pointSum_of_B3R (genT (Y.tO u u)) (NOfG Y u νL ν ng) (hB1 (max Cg₀ 0) (le_max_left _ _) D)
    (fun γ => Formalism.L2.SG.ThmBUse.J2of_nonneg' Y u u ν γ) hTB
    (ties_coreN (genT (Y.tO u u)) (NOfG Y u νL ν ng) u u A hH hTT hT hT (hA2 C' Cl hC'a hClb D large₂) hStd
      (fun _ => hctx.2.2.2.2.2.2.2.2.2) (ptTie_NOfG Y u (hP2 C' Cl hC'g hClh D large₂ X Y u hctx) νL ν ng)
      (wtTie_NOfG Y u νL ν ng A) hIre Cc hBs hθ0 hθw dg hAg zero_le_one
      (ThmBChainG.jointAmplitudeRotated_generic Y u large₂ C1 Cc hBs ν νL ng (RelPtR.relPtExPR_holds Cc u u) hM hPp hTh)
      (fun sec hs => by rw [ENNReal.ofReal_one, one_mul]; exact hNF sec hs) hs0 hka (by linarith))

end Formalism.MainStatements.RowRest
