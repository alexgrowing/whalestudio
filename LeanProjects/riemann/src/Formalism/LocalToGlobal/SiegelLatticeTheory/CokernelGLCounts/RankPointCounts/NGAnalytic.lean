import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut

namespace Formalism.L2.SG.NGAnalytic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section MassData

abbrev bk {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    S3.MassData (Formalism.L2.SG.TypedSets.TypX X) :=
  Formalism.L2.SG.MassDataConc.bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq

def unscale {P : Type} (κ : ℝ) (B : S3.MassData P) : S3.MassData P :=
  { B with Coo := B.Coo / κ, IntC := B.IntC * κ, IntN := B.IntN * κ, n0c := B.n0c / κ }

def kapU (D : D7) : ℝ := if 0 < Formalism.L2.SG.MassDataConc.kapN D then Formalism.L2.SG.MassDataConc.kapN D else 1

theorem kapU_pos (D : D7) : 0 < kapU D := by
  unfold kapU
  split_ifs with h
  · exact h
  · exact one_pos

theorem normInputs_unscale {P : Type} [Fintype P] {κ : ℝ} (hκ : 0 < κ) {B : S3.MassData P} (h : PN.NormInputs B) :
    PN.NormInputs (unscale κ B) := by
  obtain ⟨hp, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have hk : κ ≠ 0 := hκ.ne'
  refine ⟨?_, ?_, ?_, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · unfold S3.MassData.Pos at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, div_pos hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hκ, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, div_pos hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hκ, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  · show B.IntN * κ = B.volZZ / (B.unitLevelVolume * B.volPP) * (B.volPP * (B.IntC * κ))
    have e : B.IntN = B.volZZ / (B.unitLevelVolume * B.volPP) * (B.volPP * B.IntC) := h2
    rw [e]
    ring
  · show B.IntOO = B.Coo / κ * (B.IntC * κ)
    have e : B.IntOO = B.Coo * B.IntC := h3
    rw [e]
    field_simp

theorem frameInputs_unscale {P : Type} [Fintype P] {κ : ℝ} {B : S3.MassData P} {rd g : ℝ} {r k f : ℕ} {Irat Ire : ℝ}
    (h : PN.FrameInputs B rd g r k f Irat Ire) : PN.FrameInputs (unscale κ B) rd g r k f (Irat * κ) (Ire * κ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · show (B.c0 * B.c0')⁻¹ * (B.IntC * κ) = 2 ^ (f * (r + 1)) * (Irat * κ)
    rw [← mul_assoc, h4]
    ring
  · rw [h5]
    ring

theorem massDataValid_unscale {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} {P : Type} [Fintype P]
    {κ : ℝ} (hκ : 0 < κ) {B : S3.MassData P} {Irat Ire : ℝ} (h : MassDataAdmissible X Y u u' B Irat Ire) :
    MassDataAdmissible X Y u u' (unscale κ B) (Irat * κ) (Ire * κ) := by
  unfold MassDataAdmissible at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, normInputs_unscale hκ h3, frameInputs_unscale h4⟩

abbrev bkU {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    S3.MassData (Formalism.L2.SG.TypedSets.TypX X) :=
  unscale (kapU D) (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq)

def MassDataTie {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : Prop :=
  X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧ Formalism.L2.SG.LocVol.IsStdChar ψ ∧
    Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w : D.what₂.Word, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧
    Formalism.L2.SG.Pf.LocCP.LocTied D ∧ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0

def AnaAt (CSt CB : ℝ) (C1 C0n A : ℕ) {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    {P : Type} [Fintype P] (B : S3.MassData P) (Ire : ℝ) : Prop :=
  ∃ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (cSt e1 : ℝ),
    Formalism.L2.SG.RealObj.NuQOK X u u' νL ∧ Formalism.L2.SG.RealObj.NuQOK X u u' νB ∧
    0 ≤ cSt ∧ cSt ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) ∧ 0 ≤ e1 ∧ e1 ≤ 2 ∧
    AmpVanish Y u u' νL ∧
    PN.LocalInput (Y.tO u u') (NOf2 Y u u' νL νB ng) C1 C0n D.R.k ∧
    PN.GenMassInput (Y.tO u u') (NOf2 Y u u' νL νB ng) (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) e1 ∧
    PN.MeasureInput (Y.tO u u') (NOf2 Y u u' νL νB ng) cSt ∧
    PN.PointSumInput (Y.tO u u') (NOf2 Y u u' νL νB ng) (A * (D.R.rS + 1) ^ 2)
      (Real.exp (CB * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f * Real.log large₂.sc.b) * Ire)

def StepAnalyticConstants : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∀ A : ℕ, ∃ CB CSt : ℝ, 0 ≤ CB ∧ 0 ≤ CSt ∧
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∃ (P : Type) (_ : Fintype P) (B : S3.MassData P) (Irat Ire : ℝ), MassDataAdmissible X Y u u' B Irat Ire ∧
        AnaAt CSt CB C1 C0n A large₂ Y u u' B Ire

theorem ngCut2C_of_merged (hM : StepAnalyticConstants) (hS : StepSizes) (hC : StepClass) (hN : StepNormals)
    (hP : StepPoints) (hH : StepHeight) : NGCut2C := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, C0n, hA1⟩ := hM Cg cb Cw cT CT C0
  obtain ⟨CB, CSt, hCB, hCSt, a₀, b₀, hA2⟩ := hA1 (C1 + C0n + 38)
  obtain ⟨Cgs, CTs, hCg, hCT, s₀, t₀, hS2⟩ := hS Cg cb Cw cT CT C0
  obtain ⟨n₀, m₀, hN2⟩ := hN Cg cb Cw cT CT C0
  obtain ⟨p₀, q₀, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨h₀, j₀, hH2⟩ := hH Cg cb Cw cT CT C0
  refine ⟨C1, C0n, C1 + C0n + 38, CB, CSt, Cgs, CTs, hCB, hCSt, hCg, hCT, le_refl _,
    max a₀ (max s₀ (max n₀ (max p₀ h₀))), max b₀ (max t₀ (max m₀ (max q₀ j₀))),
    fun C' Cl h1 h2 D large₂ X Y u u' h0 hs hT => ?_⟩
  have hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' := ⟨h0, hs, hT⟩
  have e1' : a₀ ≤ C' := le_trans (by simp) h1
  have e2' : b₀ ≤ Cl := le_trans (by simp) h2
  have f1 : s₀ ≤ C' := le_trans (by simp) h1
  have f2 : t₀ ≤ Cl := le_trans (by simp) h2
  have i1 : n₀ ≤ C' := le_trans (by simp) h1
  have i2 : m₀ ≤ Cl := le_trans (by simp) h2
  have j1 : p₀ ≤ C' := le_trans (by simp) h1
  have j2 : q₀ ≤ Cl := le_trans (by simp) h2
  have k1 : h₀ ≤ C' := le_trans (by simp) h1
  have k2 : j₀ ≤ Cl := le_trans (by simp) h2
  obtain ⟨P, iP, B, Irat, Ire, hBk, νL, νB, ng, cSt, e1, hL, hBq, c1, c2, c3, c4, hV, hLoc, hGen, hMeas, hSum⟩ :=
    hA2 C' Cl e1' e2' D large₂ X Y u u' hc
  obtain ⟨hG, hdd, hNI, hFI⟩ := hBk
  refine ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, hL, hBq, hG, hdd, hNI, hFI,
    ngSizes_of (hS2 C' Cl f1 f2 D large₂ X Y u u' hc) c1 c2 c3 c4, ?_, hMeas, hSum⟩
  exact ⟨hC D X Y u u' hT νL νB ng, ampInput_of_vanish Y u u' νL νB ng hV,
    hN2 C' Cl i1 i2 D large₂ X Y u u' hc νL νB ng, hP2 C' Cl j1 j2 D large₂ X Y u u' hc νL νB ng, hLoc, hGen,
    hH2 C' Cl k1 k2 D large₂ X Y u u' hc νL νB ng⟩

theorem rowNGC_of_merged (hR : PN.RowNGJoint) (hCh : PN.NGChain) (hM : StepAnalyticConstants) (hE : CorankOneEquivalence)
    (hN : StepNormals) (hP : StepPoints) (hO : StepNormOne) : RowNGC :=
  counting_bound_of_joint_chain hR hCh
    (ngCut2C_of_merged hM sizes_of_hypotheses (stepClass_of_equiv hE) hN hP (stepHeight_of_normOne hO))

def TieOfCtx : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∃ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ

def NondegenerateGramTuple : Prop :=
  ∀ (D : D7) (X : HidaSetting D), ∃ X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E,
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0

theorem tieOfCtx_of (hX : NondegenerateGramTuple) : TieOfCtx := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hctx => ?_⟩
  unfold Ctx at hctx
  obtain ⟨_, _, hct⟩ := hctx
  unfold ConcTie at hct
  obtain ⟨_, _, _, _, _, _, ⟨hb, ψ, h1, h2, h3, h4, h5, h6⟩, _⟩ := hct
  obtain ⟨X0, hX0⟩ := hX D X
  exact ⟨hb, X0, ψ, by unfold MassDataTie; exact ⟨h1, h2, h3, h4, h5, h6, hX0⟩⟩

def StepChoiceConstantsC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∃ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf),
        ∃ Irat Ire : ℝ, MassDataAdmissible X Y u u' (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire

def StepAnalyticC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∀ A : ℕ, ∃ CB CSt : ℝ, 0 ≤ CB ∧ 0 ≤ CSt ∧
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
        AnaAt CSt CB C1 C0n A large₂ Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Ire

theorem merged_of (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hA : StepAnalyticC) : StepAnalyticConstants := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, CSt, hCB, hCSt, Ca, La, hA2⟩ := hA1 A
  obtain ⟨Ct, Lt, hT⟩ := hTi Cg cb Cw cT CT C0
  obtain ⟨Cb, Lb, hB1⟩ := hB Cg cb Cw cT CT C0
  refine ⟨CB, CSt, hCB, hCSt, max Ca (max Ct Cb), max La (max Lt Lb),
    fun C' Cl hC' hCl D large₂ X Y u u' hctx => ?_⟩
  simp only [max_le_iff] at hC' hCl
  obtain ⟨hb, X0, ψ, htie⟩ := hT C' Cl hC'.2.1 hCl.2.1 D large₂ X Y u u' hctx
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hok⟩ :=
    hB1 C' Cl hC'.2.2 hCl.2.2 D large₂ X Y u u' hctx hb X0 ψ htie
  have hok' := massDataValid_unscale (kapU_pos D) hok
  exact ⟨_, inferInstance, bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq, Irat * kapU D, Ire * kapU D, hok',
    hA2 C' Cl hC'.1 hCl.1 D large₂ X Y u u' hctx hb X0 ψ htie sd C Th F0 what₂ vR Q i0 i0' νq _ _ hok'⟩

end MassData

section Pin

def Pinned {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  Formalism.L2.SG.RealObj.NuQOK X u u' ν ∧ Formalism.L2.SG.RealObj.NuQPin X u u' ν

def sc {G : Type*} [MeasurableSpace G] (s : G → NNReal) (ν : G → Measure G) : G → Measure G :=
  fun γ => ((s γ : NNReal) : ENNReal) • ν γ

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

theorem Jw_sc (s : X.B.I.Ginf → NNReal) (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (w : Point D.host.E (D.R.rS + 1)) :
    Jw Y u u' (sc s ν) w = ((s (Formalism.L2.SG.RealObj.gamW X u u' w) : ℝ) : ℂ) • Jw Y u u' ν w := by
  simp only [Jw, sc, Formalism.L2.SG.TermOp.OO, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal]
  rw [← Complex.coe_smul, smul_smul, smul_smul, mul_comm]

theorem J2of_sc (s : X.B.I.Ginf → NNReal) (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (γ : PN.Pts D.host.E D.R.rS) :
    ∃ g, J2of Y u u' (sc s ν) γ = ((s g : ℝ)) ^ 2 * J2of Y u u' ν γ := by
  unfold J2of
  split_ifs with hh
  · refine ⟨Formalism.L2.SG.RealObj.gamW X u u' hh.choose, ?_⟩
    rw [Jw_sc, map_smul, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq]
  · exact ⟨1, by rw [mul_zero]⟩

theorem J2of_nonneg (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (γ : PN.Pts D.host.E D.R.rS) : 0 ≤ J2of Y u u' ν γ := by
  unfold J2of
  split_ifs
  · positivity
  · exact le_refl 0

theorem ampVanish_sc (s : X.B.I.Ginf → NNReal) (hs : ∀ γ, 0 < s γ) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (h : AmpVanish Y u u' ν) : AmpVanish Y u u' (sc s ν) := by
  intro c γ ν' h0
  apply h c γ ν'
  obtain ⟨g, hg⟩ := J2of_sc Y u u' s ν γ
  rw [hg] at h0
  have h1 : (0 : ℝ) < (s g : ℝ) := NNReal.coe_pos.mpr (hs g)
  have hpos : (0 : ℝ) < (s g : ℝ) ^ 2 := pow_pos h1 2
  rcases mul_eq_zero.mp h0 with h2 | h2
  · exact absurd h2 (ne_of_gt hpos)
  · exact h2

theorem measureInput_sc (s : X.B.I.Ginf → NNReal) (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (c : ℝ)
    (hs : ∀ γ, (s γ : ℝ) ^ 2 ≤ c) (ng : PN.Pts D.host.E D.R.rS → ℝ) :
    PN.MeasureInput (Y.tO u u') (NOf2 Y u u' (sc s ν) ν ng) c := by
  intro γ _
  refine ⟨J2of_nonneg Y u u' ν γ, ?_⟩
  obtain ⟨g, hg⟩ := J2of_sc Y u u' s ν γ
  show J2of Y u u' (sc s ν) γ ≤ c * J2of Y u u' ν γ
  rw [hg]
  exact mul_le_mul_of_nonneg_right (hs g) (J2of_nonneg Y u u' ν γ)

theorem nuQOK_sc (s : X.B.I.Ginf → NNReal) (hs1 : ∀ γ, Formalism.L2.SG.RealObj.RegX X u u' γ → s γ = 1)
    (hs0 : ∀ γ, 0 < s γ) (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (h : Formalism.L2.SG.RealObj.NuQOK X u u' ν) :
    Formalism.L2.SG.RealObj.NuQOK X u u' (sc s ν) := by
  intro γ
  obtain ⟨hreg, μR, ⟨hsf, hne, hcpl, hinv⟩, hQ⟩ := h γ
  have hs0' : s γ ≠ 0 := (hs0 γ).ne'
  refine ⟨fun hr => ?_, (s γ)⁻¹ • μR, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · show ((s γ : NNReal) : ENNReal) • ν γ = _
    rw [hs1 γ hr, ENNReal.coe_one, one_smul]
    exact hreg hr
  · haveI := hsf
    infer_instance
  · intro h0
    apply hne
    have h1 := congrArg (fun m => (s γ) • m) h0
    simpa [smul_smul, mul_inv_cancel₀ hs0'] using h1
  · simp [hcpl]
  · intro g hg
    rw [Measure.map_smul, hinv g hg]
  · intro f hf
    show _ = ∫⁻ x, (∫⁻ a, f (a * x) ∂((s γ)⁻¹ • μR)) ∂(((s γ : NNReal) : ENNReal) • ν γ)
    rw [hQ f hf, lintegral_smul_measure]
    simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul, mul_inv_cancel₀ hs0',
      ENNReal.coe_one, one_mul]

end Pin

section Steps

def StepPinExists : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' → ∃ ν, Pinned X u u' ν

def StepVanishPinned : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ ν, Pinned X u u' ν → AmpVanish Y u u' ν

def StepLocGenPinnedC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν →
      ∃ (s : X.B.I.Ginf → NNReal) (ng : PN.Pts D.host.E D.R.rS → ℝ) (e1 : ℝ),
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u' γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧ 0 ≤ e1 ∧ e1 ≤ 2 ∧
        PN.LocalInput (Y.tO u u') (NOf2 Y u u' (sc s ν) ν ng) C1 C0n D.R.k ∧
        PN.GenMassInput (Y.tO u u') (NOf2 Y u u' (sc s ν) ν ng)
          (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA) e1

def StepThmBPinnedC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∀ A : ℕ, ∃ CB : ℝ, 0 ≤ CB ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν → ∀ (νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.PointSumInput (Y.tO u u') (NOf2 Y u u' νL ν ng) (A * (D.R.rS + 1) ^ 2)
          (Real.exp (CB * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f * Real.log large₂.sc.b) * Ire)

theorem stepAnalyticC_of_steps (hE : StepPinExists) (hV : StepVanishPinned) (hL : StepLocGenPinnedC)
    (hB : StepThmBPinnedC) : StepAnalyticC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, C0n, CSt, hCSt, Cl0, Ll0, hL1⟩ := hL Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, hCB, Cb0, Lb0, hB1⟩ := hB Cg cb Cw cT CT C0 A
  obtain ⟨Ce0, Le0, hE1⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨Cv0, Lv0, hV1⟩ := hV Cg cb Cw cT CT C0
  refine ⟨CB, CSt, hCB, hCSt, max Cl0 (max Cb0 (max Ce0 Cv0)), max Ll0 (max Lb0 (max Le0 Lv0)),
    fun C' Cl hC' hCl D large₂ X Y u u' hctx hb X0 ψ htie sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok => ?_⟩
  simp only [max_le_iff] at hC' hCl
  obtain ⟨ν, hν⟩ := hE1 C' Cl hC'.2.2.1 hCl.2.2.1 D large₂ X Y u u' hctx
  obtain ⟨s, ng, e1, hs1, hs0, hs2, he0, he2, hloc, hgen⟩ :=
    hL1 C' Cl hC'.1 hCl.1 D large₂ X Y u u' hctx hb X0 ψ htie sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hν
  have hvan := hV1 C' Cl hC'.2.2.2 hCl.2.2.2 D large₂ X Y u u' hctx ν hν
  have hpt := hB1 C' Cl hC'.2.1 hCl.2.1 D large₂ X Y u u' hctx hb X0 ψ htie sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire
    hok ν hν (sc s ν) ng
  refine ⟨sc s ν, ν, ng, large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f), e1,
    nuQOK_sc u u' s hs1 hs0 ν hν.1, hν.1, ?_, le_refl _, he0, he2,
    ampVanish_sc Y u u' s hs0 ν hvan, hloc, hgen, measureInput_sc Y u u' s ν _ hs2 ng, hpt⟩
  exact le_trans (sq_nonneg _) (hs2 1)

theorem rowNGC_of_pinned (hR : PN.RowNGJoint) (hCh : PN.NGChain) (hX : NondegenerateGramTuple) (hB : StepChoiceConstantsC)
    (hE : StepPinExists)
    (hV : StepVanishPinned) (hL : StepLocGenPinnedC) (hT : StepThmBPinnedC) (hQ : CorankOneEquivalence) (hN : StepNormals)
    (hP : StepPoints) (hO : StepNormOne) : RowNGC := rowNGC_of_merged hR hCh (merged_of (tieOfCtx_of hX) hB (stepAnalyticC_of_steps hE hV hL hT)) hQ hN hP hO

def StepTermVanish : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ ν, Pinned X u u' ν → ∀ t ∈ (Y.tO u u').ngSet, J2of Y u u' ν (ptPN t) = 0 → (Y.tO u u').vec t = 0

theorem ampVanish_of_term {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (h : ∀ t ∈ (Y.tO u u').ngSet, J2of Y u u' ν (ptPN t) = 0 → (Y.tO u u').vec t = 0) : AmpVanish Y u u' ν := by
  intro c γ ν' h0
  have hz : ∀ t, ((Y.tO u u').ngSet ∩ {t | clsOf Y u u' t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = ν'}).indicator
      (Y.tO u u').vec t = 0 := by
    intro t
    rw [Set.indicator_apply]
    split_ifs with ht
    · simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at ht
      apply h t ht.1
      rw [ht.2.2.1]
      exact h0
    · rfl
  unfold grpC
  simp only [hz, tsum_zero]

theorem stepVanishPinned_of_term (h : StepTermVanish) : StepVanishPinned := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C'₀, Cl₀, h1⟩ := h Cg cb Cw cT CT C0
  exact ⟨C'₀, Cl₀, fun C' Cl hC hL D large₂ X Y u u' hctx ν hν =>
    ampVanish_of_term Y u u' ν (h1 C' Cl hC hL D large₂ X Y u u' hctx ν hν)⟩

end Steps

section LocLe

def LocalInputLe {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {E : Type} [Field E] {r : ℕ}
    {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu) (C1 C0 k : ℕ) (AAre : ℝ) : Prop :=
  ∀ γ, PN.IsPt X N γ → ∀ S : Finset (Cl × Nu), ∃ L : PN.LocalNG Cl Nu, L.Basic ∧ L.NGAt C1 r k ∧
    L.MassRatioAt C0 r ∧ L.Unfold ∧ (∀ x ∈ S, N.a2 x.1 γ x.2 = L.a2 x.1 x.2) ∧ N.Hh γ = L.Htot ∧
    0 < L.ngenTot ∧ L.ngenTot ≤ AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ

theorem localInput_of_le {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {E : Type} [Field E] {r : ℕ}
    {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu) (C1 C0 k : ℕ) (AAre : ℝ) (h : LocalInputLe X N C1 C0 k AAre)
    (hng : ∀ γ, N.ngen γ = AAre * 2 * N.Hh γ ^ PN.eN r * N.n γ) : PN.LocalInput X N C1 C0 k := by
  intro γ hγ S
  obtain ⟨L, hB, hNG, hMR, hU, ha2, hH, hpos, hle⟩ := h γ hγ S
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = N.ngen γ / L.ngenTot := ⟨_, rfl⟩
  have hng' : L.ngenTot ≤ N.ngen γ := by rw [hng γ]; exact hle
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hpos, one_mul]; exact hng'
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hB
  refine ⟨{ L with V0 := L.V0 * t }, ⟨b1, b2, b3, b4, b5, mul_nonneg b6 (by linarith), b7⟩, hNG, hMR,
    fun d S' hS' => ?_, fun x hx => by
      rw [ha2 x hx]
      cases hd : L.dat x.1 x.2 <;> simp [PN.LocalNG.a2, PN.LocalNG.ampNG, hd], hH, ?_⟩
  · have h0 : 0 ≤ L.V0 * ∏ p, L.wt p (d p) :=
      mul_nonneg b6 (Finset.prod_nonneg fun p _ => b1 p (d p))
    calc ∑ x ∈ S', L.rw x.1 ≤ L.V0 * ∏ p, L.wt p (d p) := hU d S' hS'
      _ ≤ (L.V0 * ∏ p, L.wt p (d p)) * t := le_mul_of_one_le_right h0 ht1
      _ = L.V0 * t * ∏ p, L.wt p (d p) := by ring
  · show N.ngen γ = L.V0 * t * ∏ p, L.ngen p
    have e : L.V0 * t * ∏ p, L.ngen p = t * L.ngenTot := by
      unfold PN.LocalNG.ngenTot; ring
    rw [e, ht, div_mul_cancel₀ _ hpos.ne']

theorem nPt_nonneg {E : Type} [Field E] [NumberField E] [StarRing E] {r : ℕ} (rd : ℝ) (hrd : 0 < rd) (k TT : ℕ)
    (γ : PN.Pts E r) : 0 ≤ Formalism.L2.SG.RowsConc.nPt rd k TT γ := by
  unfold Formalism.L2.SG.RowsConc.nPt
  refine Finset.prod_nonneg fun w _ => mul_nonneg (pow_nonneg (mul_nonneg (by positivity) (w.1.nonneg _)) _)
    (Finset.prod_nonneg fun a _ => pow_nonneg (mul_nonneg (by positivity) (w.1.nonneg _)) _)

def StepLocPinnedC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u' γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        LocalInputLe (Y.tO u u') (NOf2 Y u u' (sc s ν) ν (fun _ => 0)) C1 C0n D.R.k
          (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA)

theorem stepLocGenPinnedC_of_loc (h : StepLocPinnedC) : StepLocGenPinnedC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, C0n, CSt, hCSt, C'₀, Cl₀, h1⟩ := h Cg cb Cw cT CT C0
  refine ⟨C1, C0n, CSt, hCSt, C'₀, Cl₀, fun C' Cl hC hL D large₂ X Y u u' hctx hb X0 ψ htie sd C Th F0 what₂ vR Q i0 i0'
    νq Irat Ire hok ν hν => ?_⟩
  obtain ⟨s, hs1, hs0, hs2, hle⟩ :=
    h1 C' Cl hC hL D large₂ X Y u u' hctx hb X0 ψ htie sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hν
  have hrd : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero _)) _
  let AAre := PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA
  let N0 := NOf2 Y u u' (sc s ν) ν (fun _ => 0)
  let ng : PN.Pts D.host.E D.R.rS → ℝ := fun γ => AAre * 2 * N0.Hh γ ^ PN.eN D.R.rS * N0.n γ
  refine ⟨s, ng, 2, hs1, hs0, hs2, by norm_num, le_refl _,
    localInput_of_le (Y.tO u u') (NOf2 Y u u' (sc s ν) ν ng) C1 C0n D.R.k AAre hle (fun γ => rfl),
    fun γ _ => ⟨?_, le_refl _⟩⟩
  exact nPt_nonneg D.host.rdE hrd _ _ _

end LocLe

theorem rowNGC_of_loc (hR : PN.RowNGJoint) (hCh : PN.NGChain) (hX : NondegenerateGramTuple) (hB : StepChoiceConstantsC) (hE : StepPinExists)
    (hT0 : StepTermVanish) (hL : StepLocPinnedC) (hT : StepThmBPinnedC) (hQ : CorankOneEquivalence) (hN : StepNormals)
    (hP : StepPoints) (hO : StepNormOne) : RowNGC := rowNGC_of_pinned hR hCh hX hB hE (stepVanishPinned_of_term hT0) (stepLocGenPinnedC_of_loc hL) hT hQ hN hP hO

end Formalism.L2.SG.NGAnalytic
