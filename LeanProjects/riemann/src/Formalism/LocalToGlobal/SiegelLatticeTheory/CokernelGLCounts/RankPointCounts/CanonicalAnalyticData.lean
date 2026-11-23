import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Gam1TieCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiniteLevelVolumeOfMeasure

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.NGAnalytic.MassDataLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Inst

variable {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

abbrev anY : AnIn :=
  anOf (Y.tO u u') (Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1) (Formalism.L2.SG.RealObj.degX X)
    ((locOf X u u' ψ).volZZ / (((locOf X u u' ψ).localVolumeArchimedean * ∏ p, (locOf X u u' ψ).localVolumeAtPlace p) * (locOf X u u' ψ).volPP) *
      ((locOf X u u' ψ).volPP * (Formalism.L2.SG.RealObj.IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D)))
    (Formalism.L2.SG.RealObj.IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D) (Formalism.L2.SG.RealObj.IntOO X u u' 1) sd C Th D.R.rS
    (Fintype.card (InfinitePlace X.B.I.F))
    ⟨KVOf X u u' vR Q (VConstants X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq),
      KtopVOf X u u' Y.M Y.δ (VConstants X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq)⟩

def FrameVolAt : Prop :=
  (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).unitLevelVolume / (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).volZZ =
    (2 * D.host.v) ^ (((D.R.f * (D.R.rS + 1) * (8 * D.R.rS ^ 2 + 10 * D.R.rS + 3) : ℕ) : ℝ) / 3) *
      (X.B.g : ℝ) ^ (D.R.f * (D.R.rS + 1) * (2 * D.R.rS + 3))

theorem kapN_pos (hg : 0 < (X.B.g : ℝ)) : 0 < Formalism.L2.SG.MassDataConc.kapN D := by
  unfold Formalism.L2.SG.MassDataConc.kapN
  have hr : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    apply Real.rpow_pos_of_pos
    exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))
  have hgS : 0 < (Formalism.MainNotions.S.Lat.gS D : ℝ) := by
    unfold Formalism.MainNotions.S.Lat.gS
    first
      | exact Nat.cast_pos.2 (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
      | exact Nat.cast_pos.2 (Nat.mul_pos D.host.g_prime.1.pos D.host.g_prime.2.pos)
      | exact Nat.cast_pos.2 (Nat.mul_pos (D.host.g_prime 0).one_lt.le (D.host.g_prime 1).one_lt.le)
  positivity

theorem massDataValid_bk_of {large₂ : SizeData₂ D} {Cg cb Cw cT CT C0 C' Cl : ℝ} (hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u')
    (hrd : 0 < 2 * D.host.v) (hg : 0 < (X.B.g : ℝ)) (hT : MassDataTie X hb X0 ψ)
    (hLS : InLevelSAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hMs : InMassesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hCol : InColumnsAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hInd : InIndicesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hVol : InVolumesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hKpp : KppVolAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hTy : InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq)
    (hPC : ProdConv X u u' ψ) (hPr : PrimX X u) (hPr' : PrimX X u') (hKap : KapX X u u')
    (hNu : Formalism.L2.SG.RealObj.InNuX X u u' 1) (hInf : Formalism.L2.SG.RealObj.InInfinityX X u u' 1)
    (hPos : (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).Pos)
    (hFV : FrameVolAt X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) :
    ∃ Irat Ire : ℝ, MassDataAdmissible X Y u u' (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire := by
  obtain ⟨hM, hψ, hStd, hMC, hLC, -, hdet⟩ := hT
  have hH : HypX X hb (Y.FN u) (Y.FN u') u u' := ⟨hM, hc.2.2.1, Y.FN_fund u, Y.FN_fund u'⟩
  have hk := kapN_pos X hg
  have hDst : (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).Dstar = DstC X :=
    Formalism.L2.SG.IntegralApproximation.MassDataDstarX_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq
      (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq) hH hKpp
  set B := bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq with hB
  have hCoo : 0 ≤ Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 := by
    unfold Formalism.L2.SG.RealObj.DisintegrationConstant
    split_ifs with h
    · exact h.choose_spec.1.le
    · exact le_rfl
  have hdeg : 0 < B.deg := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hPos
    exact h
  have hNI : PN.NormInputs B := by
    refine ⟨hPos, rfl, ?_, ?_, ?_, hLS hH, hMs hH, hCol hH, ?_, ?_, hInd hH⟩
    · show Formalism.L2.SG.RealObj.IntOO X u u' 1 =
        Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 *
          (Formalism.L2.SG.RealObj.IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D)
      unfold Formalism.L2.SG.RealObj.IntOO Formalism.L2.SG.RealObj.IntC
      rw [hNu, ENNReal.toReal_mul, ENNReal.toReal_ofReal hCoo]
      field_simp
    · show Formalism.L2.SG.RealObj.IntOO X u u' 1 ≤ 1 / Formalism.L2.SG.RealObj.degX X
      have hd : 0 < Formalism.L2.SG.RealObj.degX X := hdeg
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hInf.2.2
    · exact inVolumes_of_compat X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ)
        (anY X Y u u' ψ sd C Th vR Q i0 i0' νq) hVol hH ⟨ψ, hψ, hStd, hMC⟩ hdet
    · exact inOrdinary_bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq hPC
    · exact hTy hH hPC (locTieX_of X ψ u (hLC u) hPr) (locTieX_of X ψ u' (hLC u') hPr')
        (typFacts_of X u u' (Formalism.L2.SG.Pf.gSplitX_holds X) (tCongX X u u') hKap)
  have hLam : 0 < PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f *
      (2 * D.host.v) ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3) := by
    unfold PN.abelian₂
    exact mul_pos (pow_pos hrd _) (Real.rpow_pos_of_pos hrd _)
  refine ⟨(B.c0 * B.c0')⁻¹ * B.IntC / 2 ^ (D.R.f * (D.R.rS + 1)),
    (B.c0 * B.c0')⁻¹ * B.IntC / 2 ^ (D.R.f * (D.R.rS + 1)) /
      (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f *
        (2 * D.host.v) ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3)), ?_, ?_, hNI, ?_⟩
  · exact Formalism.L2.SG.IntegralApproximation.Gam1TieC_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ sd C Th vR Q Y.M Y.δ i0 i0' νq Y
  · show B.d * B.d' / B.Dstar = duC X Y u * duC X Y u' / DstC X
    rw [hDst]
    rfl
  · have hL1 : PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f ≠ 0 := by
      unfold PN.abelian₂; exact (pow_pos hrd _).ne'
    have hL2 : (2 * D.host.v) ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3) ≠ 0 :=
      (Real.rpow_pos_of_pos hrd _).ne'
    refine ⟨hrd, hg, hFV, ?_, ?_⟩
    · field_simp
    · field_simp

end Inst

section Closed

def pairSys0 {D : D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂ :=
  ⟨Empty, Empty.elim, Empty.elim, fun p => p.elim, fun p => p.elim, fun _ => False⟩

def idx0 (D : D7) : Fin D.R.k := ⟨0, by have := D.R.m_add_three_le_k; omega⟩

abbrev bk0 {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) :
    S3.MassData (TypX X) :=
  bk X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u))
    (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)

abbrev canonicalAnalyticData {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : AnIn :=
  anY X Y u u' ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u))
    (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)

def OnTied (P : ∀ (D : D7) (X : HidaSetting D), Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I → Full X → D.what₂.Word → D.what₂.Word →
    (Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) → AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ → Prop) : Prop :=
  ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ → P D X hb Y u u' X0 ψ

theorem stepChoiceDataC_of
    (hLS : OnTied fun _ X hb Y u u' X0 ψ =>
      InLevelSAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (canonicalAnalyticData X Y u u' ψ))
    (hMs : OnTied fun _ X hb Y u u' X0 ψ =>
      InMassesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (canonicalAnalyticData X Y u u' ψ))
    (hCol : OnTied fun _ X hb Y u u' X0 ψ =>
      InColumnsAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (canonicalAnalyticData X Y u u' ψ))
    (hInd : OnTied fun _ X hb Y u u' X0 ψ =>
      InIndicesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (canonicalAnalyticData X Y u u' ψ))
    (hVol : OnTied fun _ X hb Y u u' X0 ψ =>
      InVolumesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (canonicalAnalyticData X Y u u' ψ))
    (hKpp : OnTied fun _ X hb Y u u' X0 ψ =>
      KppVolAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (canonicalAnalyticData X Y u u' ψ))
    (hTy : OnTied fun D X hb Y u u' X0 ψ =>
      InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u)
        (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0))
    (hPC : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ)
    (hPr : OnTied fun _ X _ _ u u' _ _ => PrimX X u ∧ PrimX X u')
    (hKap : OnTied fun _ X _ _ u u' _ _ => KapX X u u')
    (hNu : OnTied fun _ X _ _ u u' _ _ => Formalism.L2.SG.RealObj.InNuX X u u' 1 ∧ Formalism.L2.SG.RealObj.InInfinityX X u u' 1)
    (hPos : OnTied fun _ X hb Y u u' X0 ψ => (bk0 X hb Y u u' X0 ψ).Pos)
    (hFV : OnTied fun D X hb Y u u' X0 ψ =>
      FrameVolAt X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0)
        (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)) :
    StepChoiceConstantsC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨Cgs, CTs, _, _, C'₀, Cl₀, hsz⟩ := Formalism.L2.SG.NGCut.sizes_of_hypotheses Cg cb Cw cT CT C0
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u u' hc hb X0 ψ hT => ?_⟩
  have hS := hsz C' Cl h1 h2 D large₂ X Y u u' hc
  unfold SizesRec at hS
  obtain ⟨_, _, hrd, _, hg1, _⟩ := hS
  have hg : 0 < (X.B.g : ℝ) := lt_of_lt_of_le one_pos hg1
  refine ⟨0, 0, 1, X.Fu u, Y.what₂ u, fun _ => 0, pairSys0 u u' (X.Fu u) (Y.what₂ u), fun _ => idx0 D,
    fun _ => idx0 D, fun _ => 0, ?_⟩
  exact massDataValid_bk_of X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0)
    (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0) hc hrd hg hT
    (hLS Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hMs Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hCol Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hInd Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hVol Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hKpp Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hTy Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT)
    (hPC Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hPr Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT).1 (hPr Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT).2 (hKap Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hNu Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT).1 (hNu Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT).2
    (hPos Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT) (hFV Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT)

end Closed

end Formalism.L2.SG.NGAnalytic.MassDataLemmas
