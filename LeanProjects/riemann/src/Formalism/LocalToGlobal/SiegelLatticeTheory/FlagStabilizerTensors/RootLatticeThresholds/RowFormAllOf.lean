import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.Regroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.LiftRowCohD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LemmaVLift
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PointRegroupPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LiftMassCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LiftAtSome
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActRow
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AmpIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SummableLogAlpD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormTransp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrameAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictOut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LiftPhaseAgreement
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPinG
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormRepX
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DFrameAtPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AutLzNonempty
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassAbs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowsSumCPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsPt

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm Formalism.L2.SG.Pf.RowForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ampValLowerC_of {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (hNF : NormalFormC X Y u u' vR i0 i0' νq κ) (hAt : AtPtRelevantC X Y u u')
    (hpos : 0 < Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) :
    Formalism.L2.SG.Pf.RowForm.ClassAbs.AmpValLowerC X Y u u' vR i0 i0' νq := by
  refine ⟨_, hpos, fun s hgen hG => ?_⟩
  by_cases hrel : s.relevant
  · have hGt : (Y.tO u u').G s ≠ 0 := by
      show Formalism.L2.SG.TermOp.Gt s ≠ 0
      unfold Formalism.L2.SG.TermOp.Gt
      have e : (if s.G = 0 then (0 : ℝ) else 1) = 1 := if_neg hG
      rw [e]
      exact one_ne_zero
    let s' : LiftT X Y u u' κ ((Y.tO u u').rowOf s) (κ s.toTerm) := ⟨s, hGt, hgen, rfl, rfl⟩
    obtain ⟨A, B, h⟩ := hNF _ _ s' hrel
    have hamp : Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s =
        ((Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) •
          chiOO X Y u u' s := rfl
    rw [hamp, h]
    unfold frameVal
    rw [map_smul, map_smul, norm_smul, norm_smul, Formalism.L2.SG.Pf.RowForm.ClassFrameOperators.norm_hsEmb_conj,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  · have hc0 := cTerm_irrel X Y u u' vR hAt s.toTerm hrel
    rw [hc0, norm_zero, zero_mul, mul_zero]
    exact norm_nonneg _

theorem ngFac_pos (D : D7) : 0 < ngFac D := by
  unfold ngFac
  apply pow_pos
  apply Real.sqrt_pos.mpr
  apply abs_pos.mpr
  have hn : (Formalism.MainNotions.S.Lat.gS D : ℕ) ≠ 0 := by
    first | exact (Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D).ne' | exact_mod_cast (Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D).ne'
  have h0 : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hn
  exact_mod_cast (Algebra.norm_ne_zero_iff.mpr (pow_ne_zero _ h0))

theorem unram_of_splitsCompl (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (h : Formalism.MainNotions.S.SplitsCompl E p) : Formalism.L2.SG.LemmaN.Unram E p := by
  unfold Formalism.MainNotions.S.SplitsCompl at h
  unfold Formalism.L2.SG.LemmaN.Unram
  intro Q hQ _
  have hover : Ideal.span {(p : ℤ)} = Q.under ℤ := Ideal.LiesOver.over
  have hpZ : (p : ℤ) ∈ Q.under ℤ := hover ▸ Ideal.mem_span_singleton_self _
  have hpQ : ((p : ℕ) : NumberField.RingOfIntegers E) ∈ Q := by
    have h1 : algebraMap ℤ (NumberField.RingOfIntegers E) (p : ℤ) ∈ Q := hpZ
    simpa using h1
  have hne : Q ≠ ⊥ := by
    intro hb
    rw [hb, Ideal.mem_bot] at hpQ
    exact hp.ne_zero (by exact_mod_cast hpQ)
  have hmax : Q.IsMaximal := Ideal.IsPrime.isMaximal hQ hne
  obtain ⟨-, hsq⟩ := h Q hmax hpQ
  rw [← Ideal.ramificationIdx_eq_ramificationIdx' (p := Ideal.span {(p : ℤ)})]
  apply Ideal.ramificationIdx_spec
  · rw [pow_one, Ideal.map_le_iff_le_comap]
    exact le_of_eq hover
  · intro hle
    apply hsq
    have hm : algebraMap ℤ (NumberField.RingOfIntegers E) (p : ℤ) ∈
        Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers E)) (Ideal.span {(p : ℤ)}) :=
      Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
    simpa using hle hm
  all_goals first
    | exact (Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast hp.ne_zero))
    | exact (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
    | exact (0 : ℕ)

theorem rowFormC_of_leaves3 {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) (nc : ℝ)
    (hκ : Formalism.L2.SG.DataInst.RowLabel κ) (hi : ∀ v, i0 v = i0' v)
    (hPR : Formalism.L2.SG.RealObj.PtRepExists X u u' 1 i0 i0') (hNuP : Formalism.L2.SG.RealObj.NuQPin X u u' νq)
    (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k)
    (hAbs : Formalism.L2.SG.TermOp.AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u'))
    (hg : ∀ i, 3 ≤ D.host.g i ∧ Formalism.L2.SG.LemmaN.Unram D.host.E (D.host.g i))
    (hPT : PhaseTieC X Y u u' κ) (hVP : Formalism.L2.SG.VolPin.VolumeOddGeneric)
    (hPH : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u'))
    (hNR : Formalism.L2.SG.PairVal.NormRepExists D u u' (X.Fu u) (Y.what₂ u))
    (hVA : VIndepAtC X u u' i0 i0' νq 1)
    (hN : NcTieC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th
      (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) Q Y.M Y.δ i0 i0' νq nc)
    (hLT : Formalism.L2.SG.Pf.LocCP.LocTied D) (hV : 0 < X.volK2)
    (hc0 : 0 < (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th
        (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) Q Y.M Y.δ i0 i0' νq).c0 *
      (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th
        (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) Q Y.M Y.δ i0 i0' νq).c0')
    (hnc : 0 < nc) (hα : 0 < ∏' q, Formalism.L2.SG.DataInst.alpD u u' q) :
    RowFormC X hb Y u u' X0 ψ sd C Th (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) Q Y.M Y.δ i0 i0' νq
      κ nc := by
  set vR := Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M with hvR
  have hDict : Formalism.L2.SG.Pf.IotaDictC := Formalism.L2.SG.Pf.iotaDictC_holds
  have hRC : Formalism.L2.SG.Pf.RelCharC := Formalism.L2.SG.Pf.RelChar.relCharC_holds
  have hAtS := Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u'
  have hTP : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) (w : Point D.host.E (D.R.rS + 1)), t.atPt w →
      Formalism.MainNotions.S.LocalSplitGroups.TotPos (Formalism.MainNotions.S.LocalSplitGroups.Gpt (D.mem u).A.T (D.mem u').A.T w) :=
    fun t w h => Formalism.L2.SG.WConst.atPt_totPos t w h
  have hCPU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u) :=
    fun t w w' h h' => Formalism.L2.SG.RowsAbsX.atPt_uniq _ _ _ t.cls w w' h h'
  have hDF : DFrameAtS X u u' i0 i0' 1 := by
    have hi' : i0' = i0 := funext fun v => (hi v).symm
    subst hi'
    exact Formalism.L2.SG.Pf.Carrier.dual_frame_at_places X u u' 1 i0'
  have hFT : FormTranspC X Y u u' vR νq κ :=
    Formalism.L2.SG.Pf.formula_transport_of_condition X Y u u' νq κ hNuP hVP (fun i => (hg i).1) hPH hRC
      (RealDecompL.liftDecompC_of_atSome X Y u u' κ hAtS) (liftAtSomeC_holds X Y u u' κ) hNR hCPU
  have hScal : ScalTC X Y u u' κ :=
    Formalism.L2.SG.Pf.RowForm.ScalT.scalTC_of X Y u u' κ hκ (liftIotaC_of hDict X Y u u') hg
  have hCF : ClassFrameC X hb Y u u' X0 ψ sd C Th vR Q Y.M Y.δ i0 i0' νq κ :=
    classFrameC_all X hb Y u u' X0 ψ sd C Th vR Q Y.M Y.δ i0 i0' νq κ hAtS hTP hCPU hDF hPT hFT hVA hScal
      (Formalism.L2.SG.Pf.LiftCellVolume.LemmaVLiftC_holds X Y u u' κ) (atPtRelevantC_holds X Y u u') hV hc0.le
  have hNF : NormalFormC X Y u u' vR i0 i0' νq κ :=
    normalFormC_all X Y u u' vR i0 i0' νq κ hAtS hTP hCPU hDF hPT hFT
  have hscl : 0 < Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 := by
    rw [classFrame_scl X hb Y u u' X0 ψ sd C Th vR Q Y.M Y.δ i0 i0' νq hV]
    exact inv_pos.2 (Real.sqrt_pos.2 hc0)
  have hAV := ampValLowerC_of X Y u u' vR i0 i0' νq κ hNF (atPtRelevantC_holds X Y u u') hscl
  have hDictIff : IotaDictIff := fun D X Y u u' s₁ s₂ => hDict D X Y u u' s₁ s₂
  have hMass := Formalism.L2.SG.Pf.FibreCounting.LiftMassC_holds X Y u u'
  have hRR : RowRegroupC X Y u u' κ := rowRegroupC_of X Y u u' κ hAbs hScal
  have hIF : LiftIotaFreeC X Y u u' := fun s₁ s₂ _ h hr =>
    Formalism.L2.SG.Pf.Act.liftIotaFree (fun u'' => Formalism.L2.SG.Closed.NeatKu_holds X u'' Y.hK)
      Formalism.L2.SG.Pf.iotaRepC_holds u u' s₁ s₂ h hr
  have hTor : TorsorC X Y u u' vR i0 i0' νq κ :=
    torsorC_of X Y u u' vR i0 i0' νq κ hκ hIF hMass (liftRowCohC_of_dict X Y u u' hDictIff)
  have hCA : ClassAbsC X Y u u' vR i0 i0' νq κ :=
    Formalism.L2.SG.Pf.RowForm.ClassAbs.classAbsC_of X Y u u' vR i0 i0' νq κ hAbs hAV hMass
  have hS : SigRowsC X hb Y u u' X0 ψ sd C Th vR Q Y.M Y.δ i0 i0' νq κ :=
    sigRowsC_of X hb Y u u' X0 ψ sd C Th vR Q Y.M Y.δ i0 i0' νq κ hRR hCF hTor hCA hc0
  have hW : WeightConstC X Y u u' (nc * ∏' q, Formalism.L2.SG.DataInst.alpD u u' q) :=
    Formalism.L2.SG.WConst.weightConstC_of X Y u u' _ hPR (Formalism.L2.SG.WConst.eligTotPos_holds X Y u u')
  have hRV : RowVecC X Y u u' vR i0 i0' νq κ nc :=
    rowVecC_of X Y u u' vR i0 i0' νq κ nc hW (Formalism.L2.SG.WConst.pointRegroupC_of X Y u u' vR i0 i0' νq κ hCA)
      (Formalism.L2.SG.RhoPf.massRows_pos X Y u) (Formalism.L2.SG.WConst.kapN_pos (D := D)) (mul_pos hnc hα) (ngFac_pos D)
  have hR : RhoTieC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq :=
    Formalism.L2.SG.MassDataConc.RhoTieC_holds X hb Y u u' X0 ψ sd C Th vR Q Y.M Y.δ i0 i0' νq
      (Formalism.L2.SG.Pf.latRowLat X u) (Formalism.L2.SG.Pf.latInj X u) (Formalism.L2.SG.Pf.latSurj X u)
  have hA : AlTieC X hb Y u u' X0 ψ sd C Th vR Q Y.M Y.δ i0 i0' νq :=
    Formalism.L2.SG.Pf.AlTieC_of_loc X hb Y u u' X0 ψ sd C Th _ Q Y.M Y.δ i0 i0' νq hLT hk
  exact rowFormC_of X hb Y u u' X0 ψ sd C Th vR Q Y.M Y.δ i0 i0' νq κ nc hS hRV hN hR hA hnc hα
    (Formalism.L2.SG.WConst.kapN_pos (D := D)) (Formalism.L2.SG.RhoPf.massRows_pos X Y u) (ngFac_pos D)

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups ValuativeRel Formalism.L2.SG.SpectralTiesReal
open Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def VIndepAtAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k)
    (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf),
    u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y → (∀ v, i0 v = i0' v) → NuQPin T.X u u' νq →
      Formalism.L2.SG.Pf.RowForm.VIndepAtC T.X u u' i0 i0' νq 1

def GUnramAll : Prop :=
  ∀ (D : D7) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ i : Fin 2, Formalism.L2.SG.LemmaN.Unram D.host.E (D.host.g i)

theorem gUnramAll : GUnramAll := by
  intro D u u' hS i
  unfold Formalism.MainNotions.S.Cnt.Stand at hS
  obtain ⟨hg0, hg1, -, hsp, -⟩ := hS.2.2.2.2.2.2.2
  have hpr : Nat.Prime (D.host.g i) := by
    fin_cases i
    · exact hg0
    · exact hg1
  exact Formalism.L2.SG.Pf.unram_of_splitsCompl D.host.E (D.host.g i) hpr (hsp i)

def NormalizingConstantPositiveAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E)
    (C Th : ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u))
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf) (Lsp : LocSp D T.Y.M)
    (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]),
    u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE T.X.B.I.cm.sig T.X.B.I.J X0).det ≠ 0 →
    2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
    (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq → (∀ p, Irreducible (ϖ p)) →
      Formalism.L2.SG.MassDataConc.NcTieC T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ (T.Y.tO u u')
        (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
        (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq
        (Formalism.L2.SG.Pf.Cnt.cExpl D (T.X.Fu u) (T.Y.what₂ u)) ∧
      0 < (Formalism.L2.SG.MassDataConc.bCF T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ (T.Y.tO u u')
        (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
        (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq).c0 *
        (Formalism.L2.SG.MassDataConc.bCF T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ (T.Y.tO u u')
        (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
        (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq).c0'

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
