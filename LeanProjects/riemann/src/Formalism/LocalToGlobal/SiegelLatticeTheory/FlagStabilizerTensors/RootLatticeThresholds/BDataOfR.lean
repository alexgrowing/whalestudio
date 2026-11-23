import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmBUseR
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.JointAmplitudePoints

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.BDat Formalism.L2.SG.ThmBUseR
open scoped ENNReal

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.BDatR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section J2

variable {D : D7}

def JointAmplitudeFactorizationRotated {τ₀ Rw I₀ H H₁ : Type} [Fintype I₀] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ₀ Rw I₀ H H₁)
    {Cl Nu : Type} (N : Formalism.FourierDecayAlt.PN.NGData τ₀ D.host.E D.R.rS Cl Nu) (large₂ : SizeData₂ D) (C1 : ℝ)
    (W : D.what₂.Tau → LocW D.R.k D.R.rS) (A : ∀ τ, LocS (W τ)) (T T' : ℕ) (Cfac : ℝ) : Prop :=
  ∀ γ (w : Point D.host.E (D.R.rS + 1)), Formalism.FourierDecayAlt.PN.IsPt X N γ → Formalism.L2.SG.RowsConc.toPts w = γ →
    Formalism.L2.SG.ThmBUse.IsRowPt D T T' w → 0 < N.jacobianSquareBound γ →
    ∃ (g : D.what₂.Tau → MatKR D.R.k D.R.rS) (θ' : D.what₂.Tau → ℝ)
      (νR : D.what₂.Tau → Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
      (∀ τ, RelPt D (W τ).z (W τ).z' (g τ) (ptLoc D τ w) ∧ normWin D large₂ C1 (θ' τ) ∧
        RMeas D (W τ) (g τ) (θ' τ) (νR τ)) ∧
      ENNReal.ofReal (N.jacobianSquareBound γ) ≤ ENNReal.ofReal Cfac * ∏ τ, ENNReal.ofReal (hsNormSq ((A τ).J (νR τ) (g τ)))

private lemma prod_ofReal_le_lemma {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ∏ i ∈ s, ENNReal.ofReal (x i) ≤ ENNReal.ofReal (∏ i ∈ s, x i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.prod_insert ha]
  rcases le_or_gt 0 (x a) with h | h
  · rw [ENNReal.ofReal_mul h]; gcongr
  · rw [ENNReal.ofReal_of_nonpos h.le, zero_mul]; simp

theorem jointAmplitude_bound_rotated {τ₀ Rw I₀ H H₁ : Type} [Fintype I₀] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ₀ Rw I₀ H H₁)
    {Cl Nu : Type} (N : Formalism.FourierDecayAlt.PN.NGData τ₀ D.host.E D.R.rS Cl Nu) {large₂ : SizeData₂ D} {C1 Ca Ch Cg b : ℝ}
    {u u' : D.what₂.Word} {θ : ℝ} {hT : 0 < Tr D u} {hT' : 0 < Tr D u'} (I : AmpIn large₂ C1 Ca u u' θ hT hT')
    (hok : ∀ τ, LocOk D Ch Cg (I.L τ) (lamSH D.R (D.hc τ)) (kaRe D) b (kaRe D))
    (hka : 0 < Formalism.MainNotions.S.Bridge.kaS D) {Cfac : ℝ} (hCfac : 0 ≤ Cfac)
    (hF : JointAmplitudeFactorizationRotated X N large₂ C1 I.W I.A (D.mem u).A.T (D.mem u').A.T Cfac) :
    JointNormBoundRotated X N (bdOf I.toInputs hok) (Cfac * ∏ τ, (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))) := by
  intro γ w hpt hw hrow
  by_cases hpos : 0 < N.jacobianSquareBound γ
  · obtain ⟨g, θ', νR, hτ, hle⟩ := hF γ w hpt hw hrow hpos
    have h1 : ∏ τ, ENNReal.ofReal (hsNormSq ((I.A τ).J (νR τ) (g τ))) ≤
        ∏ τ, (ENNReal.ofReal (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) *
          orbSq ((bdOf I.toInputs hok).L τ) ((bdOf I.toInputs hok).f τ)
            (Formalism.MainNotions.S.Pv.Frames.turnPt (ptLoc D τ w))) := by
      apply Finset.prod_le_prod'
      intro τ _
      exact le_trans (I.hJ τ (g τ) (ptLoc D τ w) (hτ τ).1 (θ' τ) (hτ τ).2.1 (νR τ) (hτ τ).2.2)
        (by gcongr; exact orbSqO_le_bdOf I.toInputs hok hka τ _)
    rw [Finset.prod_mul_distrib] at h1
    have h2 := prod_ofReal_le_lemma Finset.univ (fun τ => I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))
    calc ENNReal.ofReal (N.jacobianSquareBound γ)
        ≤ ENNReal.ofReal Cfac * ∏ τ, ENNReal.ofReal (hsNormSq ((I.A τ).J (νR τ) (g τ))) := hle
      _ ≤ ENNReal.ofReal Cfac * ((∏ τ, ENNReal.ofReal (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))) *
          ∏ τ, orbSq ((bdOf I.toInputs hok).L τ) ((bdOf I.toInputs hok).f τ)
            (Formalism.MainNotions.S.Pv.Frames.turnPt (ptLoc D τ w))) := by gcongr
      _ ≤ ENNReal.ofReal Cfac * (ENNReal.ofReal (∏ τ, (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))) *
          ∏ τ, orbSq ((bdOf I.toInputs hok).L τ) ((bdOf I.toInputs hok).f τ)
            (Formalism.MainNotions.S.Pv.Frames.turnPt (ptLoc D τ w))) := by gcongr
      _ = ENNReal.ofReal (Cfac * ∏ τ, (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))) *
          JSqR D (bdOf I.toInputs hok) w := by
        rw [ENNReal.ofReal_mul hCfac, mul_assoc]; rfl
  · rw [ENNReal.ofReal_of_nonpos (not_lt.mp hpos)]; simp

end J2

section Cut

open Formalism.L2.SG.Pf.JointAmplitudePoints

variable {D : D7} {X : HidaSetting D}

def RelPtExPR (u u' : D.what₂.Word) {θ : ℝ} (C : Choice X θ) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) → ∀ τ,
      RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamP C u u' w τ) (ptLoc D τ w)

private lemma toPts_inj_lemma {K : Type} [Zero K] {i : ℕ} (p q : Formalism.MainNotions.S.Point K (i + 1))
    (h : Formalism.L2.SG.RowsConc.toPts p = Formalism.L2.SG.RowsConc.toPts q) : p = q := by
  have h1 : p.1.map Prod.snd = q.1.map Prod.snd := congrArg (fun s => s.1.blocks) h
  have key : ∀ r : Formalism.MainNotions.S.Point K (i + 1), List.ofFn (Formalism.L2.SG.RowsConc.toPts r).2 = r.1.map Prod.fst := by
    intro r
    apply List.ext_get
    · simp [Formalism.L2.SG.RowsConc.toPts, Composition.length]
    · intro n h1 h2
      simp [Formalism.L2.SG.RowsConc.toPts]
  have h2 : p.1.map Prod.fst = q.1.map Prod.fst := by
    rw [← key p, ← key q]
    exact congrArg (fun s : (Σ c : Composition (i + 1), (Fin c.length → K)) => List.ofFn s.2) h
  apply Subtype.ext
  rw [← List.zip_unzip p.1, ← List.zip_unzip q.1, List.unzip_fst, List.unzip_snd, List.unzip_fst,
    List.unzip_snd, h1, h2]

private lemma quot_scale_lemma_2 {k r : ℕ} {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (h : Formalism.MainNotions.S.IsQuotMeas μG μS ν) {c : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    Formalism.MainNotions.S.IsQuotMeas μG (c • μS) (c⁻¹ • ν) := by
  intro f hf
  rw [h f hf]
  simp only [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ hct, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem jointAmplitudeFactorizationRotated_of (Y : Full X) (u u' : D.what₂.Word) (large₂ : SizeData₂ D) (C1 : ℝ) {θ : ℝ} (C : Choice X θ)
    (hB : WuBessel C) (ν νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ)
    (hR : RelPtExPR u u' C) (hM : RMeasExP u u' C) (hP : LocalAmplitudesPositive Y u u' ν C hB) (hT : ThetaWinP Y u u' ν C hB large₂ C1) :
    JointAmplitudeFactorizationRotated (Y.tO u u') (NOf2 Y u u' νL ν ng) large₂ C1 (WX C u u') (AX hB u u') (D.mem u).A.T (D.mem u').A.T 1 := by
  intro γ w hpt hw hrow hpos
  have hJB : (NOf2 Y u u' νL ν ng).jacobianSquareBound γ = J2of Y u u' ν γ := rfl
  rw [hJB] at hpos ⊢
  subst hw
  obtain ⟨w', hw', hrep⟩ := isPtRep_of_J2of hpos
  have hww : w' = w := toPts_inj_lemma w' w hw'
  subst hww
  have hP1 : 0 < localAmplitudeProduct u u' hB w' := hP w' hrow hpos
  haveI := Formalism.L2.SG.Pf.LTL.tau_nonempty D
  have hn : 0 < Fintype.card D.what₂.Tau := Fintype.card_pos
  have hθ0 : thetaP u u' hB (J2of Y u u' ν (toPts w')) w' =
      (localAmplitudeProduct u u' hB w' / J2of Y u u' ν (toPts w')) ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)) := by
    simp only [thetaP, if_pos (And.intro hpos hP1)]
  have hθpos : 0 < thetaP u u' hB (J2of Y u u' ν (toPts w')) w' := by
    rw [hθ0]; apply Real.rpow_pos_of_pos; exact div_pos hP1 hpos
  have hν1 : ∀ τ, RMeas D (locW C u u' τ) (gamP C u u' w' τ) 1 (nu1P C u u' w' τ) := fun τ => by
    have h := hM w' hrow hrep τ
    simp only [nu1P, dif_pos h]
    exact h.choose_spec
  have hsc : ∀ τ, RMeas D (locW C u u' τ) (gamP C u u' w' τ) (thetaP u u' hB (J2of Y u u' ν (toPts w')) w')
      (ENNReal.ofReal (thetaP u u' hB (J2of Y u u' ν (toPts w')) w')⁻¹ • nu1P C u u' w' τ) := fun τ => by
    obtain ⟨p, μR, hroot, hq⟩ := hν1 τ
    refine ⟨p, μR, hroot, ?_⟩
    rw [ENNReal.ofReal_one, one_smul] at hq
    rw [ENNReal.ofReal_inv_of_pos hθpos]
    exact quot_scale_lemma_2 hq (ENNReal.ofReal_pos.mpr hθpos).ne' ENNReal.ofReal_ne_top
  refine ⟨fun τ => gamP C u u' w' τ, fun _ => thetaP u u' hB (J2of Y u u' ν (toPts w')) w',
    fun τ => ENNReal.ofReal (thetaP u u' hB (J2of Y u u' ν (toPts w')) w')⁻¹ • nu1P C u u' w' τ,
    fun τ => ⟨hR w' hrow hrep τ, hT w' hrow hpos, hsc τ⟩, ?_⟩
  set θ0 := thetaP u u' hB (J2of Y u u' ν (toPts w')) w' with hθdef
  set J2 := J2of Y u u' ν (toPts w') with hJ2def
  have hfac : ∀ τ, hsNormSq ((AX hB u u' τ).J (ENNReal.ofReal θ0⁻¹ • nu1P C u u' w' τ) (gamP C u u' w' τ)) =
      θ0⁻¹ * θ0⁻¹ * hsNormSq ((locS hB u u' τ).J (nu1P C u u' w' τ) (gamP C u u' w' τ)) := fun τ => by
    show hsNormSq ((locS hB u u' τ).J (ENNReal.ofReal θ0⁻¹ • nu1P C u u' w' τ) (gamP C u u' w' τ)) = _
    rw [Formalism.L2.SG.Pf.LTL.locJ_smul, Formalism.L2.SG.Pf.LTL.hsNormSq_smul, Complex.normSq_ofReal,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hθpos.le)]
  have hpow : θ0 ^ (2 * Fintype.card D.what₂.Tau) = localAmplitudeProduct u u' hB w' / J2 := by
    rw [hθ0, ← Real.rpow_natCast, ← Real.rpow_mul (div_pos hP1 hpos).le]
    have : (1 : ℝ) / (2 * Fintype.card D.what₂.Tau) * ((2 * Fintype.card D.what₂.Tau : ℕ) : ℝ) = 1 := by
      push_cast; field_simp
    rw [this, Real.rpow_one]
  have hprod : ∏ τ, (θ0⁻¹ * θ0⁻¹ * hsNormSq ((locS hB u u' τ).J (nu1P C u u' w' τ) (gamP C u u' w' τ))) = J2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    change (θ0⁻¹ * θ0⁻¹) ^ Fintype.card D.what₂.Tau * localAmplitudeProduct u u' hB w' = J2
    have e : (θ0⁻¹ * θ0⁻¹) ^ Fintype.card D.what₂.Tau = (θ0 ^ (2 * Fintype.card D.what₂.Tau))⁻¹ := by
      rw [← mul_inv, ← pow_two, inv_pow, ← pow_mul]
    rw [e, hpow, inv_div, div_mul_cancel₀ _ hP1.ne']
  rw [ENNReal.ofReal_one, one_mul]
  simp only [hfac]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun τ _ => by
    have := Formalism.L2.SG.Pf.LTL.hsNormSq_nonneg ((locS hB u u' τ).J (nu1P C u u' w' τ) (gamP C u u' w' τ))
    positivity), hprod]

end Cut

section Steps

open Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf Formalism.QuantumDeterminants NumberField
  Formalism.L2.SG.Pf.MainEqCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem ties_coreR {τ₀ Rw I₀ H H₁ : Type} [Fintype I₀] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
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
    (hloc : ∀ τ, ColsTypeTr Cc u τ ∧ ColsTypeTr Cc u' τ ∧ ZTr Cc u τ ∧ ZTr Cc u' τ ∧ HaarTr Cc τ ∧
      GoodSRest hBs u u' τ)
    {Cfac : ℝ} (hCfac : 0 ≤ Cfac)
    (hJF : JointAmplitudeFactorizationRotated XT N large₂ C1 (WX Cc u u') (AX hBs u u') (D.mem u).A.T (D.mem u').A.T Cfac)
    (hNF : ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
        (∀ τ, IsSection D.R.k D.R.rS (WX Cc u u' τ).z (WX Cc u u' τ).z' (sec τ)) →
        ENNReal.ofReal Cfac * ∏ τ, MMv D u u' (AX hBs u u' τ) (sec τ) ≤
          ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire))
    (hCs : 0 ≤ Cs) (hka : 0 < Formalism.MainNotions.S.Bridge.kaS D) (hβ : 0 ≤ Cβ) :
    TiesR XT N Ch Cs (D.mem u).A.T (D.mem u').A.T (large₂.sc.b ^ Cβ) A Cb
      (Real.exp ((max 0 Cb * Cβ + |Ca| + |Cn|) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f * Real.log large₂.sc.b) * Ire) := by
  have hb : 0 < large₂.sc.b := by
    have h := Formalism.MainNotions.exp_one_le_b_rpow large₂ (Cβ := 1) le_rfl
    rw [Real.rpow_one] at h
    linarith [Real.exp_pos 1]
  have hv : 0 < D.host.v := Formalism.MainNotions.BridgeLemma.sza_v_pos D
  let I := ampInOf hAmp hH hTT hθw hT hT' (WX Cc u u') (AX hBs u u')
    (fun τ => goodW_of Cc u u' τ (hloc τ).1 (hloc τ).2.1 (hloc τ).2.2.1 (hloc τ).2.2.2.1 (hloc τ).2.2.2.2.1)
    (fun τ => goodS_of hBs u u' τ (hloc τ).2.2.2.2.2)
  have hok : ∀ τ, LocOk D Ch Cs (I.L τ) (lamSH D.R (D.hc τ)) (kaRe D) (large₂.sc.b ^ Cβ) (kaRe D) := fun τ =>
    locOk_locB D τ u u' θ _ _ _ _ hT hT' hka hv hθ0 (hStd hH τ u u').1 (hTF hH u) (hTF hH u')
  have hK : 0 ≤ ∏ τ, (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) :=
    Finset.prod_nonneg fun τ _ => mul_nonneg (I.hK τ).le (Real.rpow_nonneg hb.le _)
  refine ⟨bdOf I.toInputs hok, 1, Cfac * ∏ τ, (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)), zero_le_one,
    mul_nonneg hCfac hK, gaps_bdOf I.toInputs hok (fun τ => (hStd hH τ u u').2) hCs le_rfl, hpt, hwt,
    jointAmplitude_bound_rotated XT N I hok hka hCfac hJF, normTie_bdOf I hok hCfac hIre hβ (hNF I.sec fun τ => I.sec_spec τ)⟩

def RowBDataR {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (νB : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ (θ : ℝ) (C : Choice X θ) (hB : WuBessel C), 0 < θ ∧ normWin D large₂ C1 θ ∧
    (∀ τ, ColsTypeTr C u τ ∧ ColsTypeTr C u' τ ∧ ZTr C u τ ∧ ZTr C u' τ ∧ HaarTr C τ ∧ GoodSRest hB u u' τ) ∧
    ∃ Cfac : ℝ, 0 ≤ Cfac ∧
      (∀ (νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ),
        JointAmplitudeFactorizationRotated (Y.tO u u') (NOf2 Y u u' νL νB ng) large₂ C1 (WX C u u') (AX hB u u') (D.mem u).A.T (D.mem u').A.T Cfac) ∧
      ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
        (∀ τ, IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
        ENNReal.ofReal Cfac * ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤
          ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)

theorem rowBDataR_of {D : D7} {X : HidaSetting D} (large₂ : SizeData₂ D) (Y : Full X) (u u' : D.what₂.Word)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) (hIre : 0 ≤ Ire) {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)
    (hθ0 : 0 < θ) (hθw : normWin D large₂ C1 θ)
    (hloc : ∀ τ, ColsTypeTr C u τ ∧ ColsTypeTr C u' τ ∧ ZTr C u τ ∧ ZTr C u' τ ∧ HaarTr C τ ∧ GoodSRest hB u u' τ)
    (hR : RelPtExPR u u' C) (hM : Formalism.L2.SG.Pf.JointAmplitudePoints.RMeasExP u u' C)
    (hP : Formalism.L2.SG.Pf.JointAmplitudePoints.LocalAmplitudesPositive Y u u' ν C hB) (hT : Formalism.L2.SG.Pf.JointAmplitudePoints.ThetaWinP Y u u' ν C hB large₂ C1)
    (hN : ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
        (∀ τ, IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
        ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤ ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)) :
    RowBDataR large₂ Y u u' ν C1 Cn Ire := ⟨hIre, θ, C, hB, hθ0, hθw, hloc, 1, zero_le_one,
    fun νL ng => jointAmplitudeFactorizationRotated_of Y u u' large₂ C1 C hB ν νL ng hR hM hP hT,
    fun sec hsec => by rw [ENNReal.ofReal_one, one_mul]; exact hN sec hsec⟩

def RowBDataUnifR : Prop :=
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
      ∀ ν, Pinned X u u' ν → RowBDataR large₂ Y u u' ν C1 Cn Ire

def RowBDataGR (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (νB : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ (θ : ℝ) (C : Choice X θ) (hB : WuBessel C), 0 < θ ∧ normWin D large₂ C1 θ ∧
    (∀ τ, ColsTypeTr C u τ ∧ ColsTypeTr C u τ ∧ ZTr C u τ ∧ ZTr C u τ ∧ HaarTr C τ ∧ GoodSRest hB u u τ) ∧
    ∃ Cfac : ℝ, 0 ≤ Cfac ∧
      (∀ (νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ),
        JointAmplitudeFactorizationRotated (genT (Y.tO u u)) (NOfG Y u νL νB ng) large₂ C1 (WX C u u) (AX hB u u) (D.mem u).A.T (D.mem u).A.T Cfac) ∧
      ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
        (∀ τ, IsSection D.R.k D.R.rS (WX C u u τ).z (WX C u u τ).z' (sec τ)) →
        ENNReal.ofReal Cfac * ∏ τ, MMv D u u (AX hB u u τ) (sec τ) ≤
          ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)

def RowBDataUnifGR : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 Cn : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν → RowBDataGR large₂ Y u ν C1 Cn Ire

theorem stepThmBPinnedC_ofR (hB : JointNormBoundRotatedUniform) (hA : AmpUnif) (hP : PtUnif)
    (hR : RowBDataUnifR) : StepThmBPinnedC := by
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
  obtain ⟨hIre, θ, Cc, hBs, hθ0, hθw, hloc, Cfac, hCfac, hJF, hNF⟩ :=
    hR2 C' Cl hC'c hCld D large₂ X Y u u' hctx hb X0 ψ hBT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBO ν hpin
  have hTB : 0 ≤ Real.exp ((max 0 Cb * max 2 Cw + |Ca| + |Cn|) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f *
      Real.log large₂.sc.b) * Ire := mul_nonneg (Real.exp_pos _).le hIre
  exact pointSum_of_B3R (Y.tO u u') (NOf2 Y u u' νL ν ng) (hB1 (max Cg₀ 0) (le_max_left _ _) D)
    (fun γ => Formalism.L2.SG.ThmBUse.J2of_nonneg' Y u u' ν γ) hTB
    (ties_coreR (Y.tO u u') (NOf2 Y u u' νL ν ng) u u' A hH hTT hT hT' (hA2 C' Cl hC'a hClb D large₂) hStd
      (fun _ => hctx.2.2.2.2.2.2.2.2.2) (point_amplitude_relation_normalized Y u u' (hP2 C' Cl hC'g hClh D large₂ X Y u u' hctx) νL ν ng)
      (Formalism.L2.SG.ThmBUse.weight_normalized Formalism.L2.SG.Pf.weightConclusion Y u u' νL ν ng A) hIre Cc hBs hθ0 hθw hloc hCfac
      (hJF νL ng) hNF hs0 hka (by linarith))

theorem stepThmBG_ofR (hB : JointNormBoundRotatedUniform) (hA : AmpUnif) (hP : PtUnifG)
    (hR : RowBDataUnifGR) : StepThmBG := by
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
  obtain ⟨hIre, θ, Cc, hBs, hθ0, hθw, hloc, Cfac, hCfac, hJF, hNF⟩ :=
    hR2 C' Cl hC'c hCld D large₂ X Y u hctx hb X0 ψ hBT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBO ν hpin
  have hTB : 0 ≤ Real.exp ((max 0 Cb * max 2 Cw + |Ca| + |Cn|) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f *
      Real.log large₂.sc.b) * Ire := mul_nonneg (Real.exp_pos _).le hIre
  exact pointSum_of_B3R (genT (Y.tO u u)) (NOfG Y u νL ν ng) (hB1 (max Cg₀ 0) (le_max_left _ _) D)
    (fun γ => Formalism.L2.SG.ThmBUse.J2of_nonneg' Y u u ν γ) hTB
    (ties_coreR (genT (Y.tO u u)) (NOfG Y u νL ν ng) u u A hH hTT hT hT (hA2 C' Cl hC'a hClb D large₂) hStd
      (fun _ => hctx.2.2.2.2.2.2.2.2.2) (ptTie_NOfG Y u (hP2 C' Cl hC'g hClh D large₂ X Y u hctx) νL ν ng)
      (wtTie_NOfG Y u νL ν ng A) hIre Cc hBs hθ0 hθw hloc hCfac (hJF νL ng) hNF hs0 hka (by linarith))

end Steps

end Formalism.L2.SG.Pf.BDatR
