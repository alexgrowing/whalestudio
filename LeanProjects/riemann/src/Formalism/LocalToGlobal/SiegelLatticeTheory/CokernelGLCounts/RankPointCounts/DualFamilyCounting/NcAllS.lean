import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSplitS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSSplitPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWitt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXConditions
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXVolH
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieIdx
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdFull
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolVFinal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTHoldsX
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcReal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieLG

noncomputable section

namespace Formalism.L2.SG.Pf.NcAllS

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

set_option maxHeartbeats 4000000 in
variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncTieAllS_of (hSplit : Formalism.L2.SG.Pf.NcSplitS.SplitOm) (hRB : Formalism.L2.SG.Pf.NcReal.RealBracket)
    (hHyp : HypX X hb FdN FdN' u u') (hMC : MeasCompatψ X ψ) (hStd : StdHyp X.B.I.cm.sig X.B.I.J ψ)
    (hLat : ∃ L : Submodule (NumberField.RingOfIntegers X.B.I.E) (Fin X.B.I.n → X.B.I.E),
      Submodule.IsLattice X.B.I.E L ∧ (L : Set (Fin X.B.I.n → X.B.I.E)) = (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    (hdet : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0)
    (hSW1 : Formalism.MainNotions.UnusedSlot34.SWa1 X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J)
    (hSW2 : Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J)
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (hM : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass)
    (hMs : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses)
    (hL : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS)
    (hO : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InOrdinary)
    (hTy : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped)
    (hV : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes)
    (hVG : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG)
    (hcong : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hRR : IsRowReps D F0 what₂)
    (hVo : Formalism.L2.SG.Pf.NcVal.VolOrdV X u u' ψ) (hVt : Formalism.L2.SG.Pf.NcVal.VolTypV X u u' ψ)
    (hIx : Formalism.L2.SG.Pf.NcIdx.IndexTypC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hOm : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ) (hFD : Formalism.L2.SG.Pf.NcVal.FieldDict X u u')
    (hPC : ProdConv X u u' ψ) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) := by
  obtain ⟨⟨hT1, νH, hOmT, hCT⟩, -⟩ := hMC.1 u'
  have hn : X.B.I.n = D.R.r := hFD.2.2.2.2.2.2.1
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hn2 : 2 * (D.R.rS + 1 + D.R.rS) < X.B.I.n := by rw [hn]; omega

  have hp := hP.1
  have hKo := hP.2.1
  have hprod : 0 < ∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _) p.1)).toReal :=
    Finset.prod_pos fun p _ => (hp p).2.2.2.2.2.1
  have hKf : 0 < (X.measG.μGf (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _))).toReal := by
    have h := hKo
    change 0 < (X.measG.μGf (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _))).toReal / _ at h
    exact (div_pos_iff_of_pos_right hprod).1 h
  obtain ⟨hK0, hKtop⟩ := ENNReal.toReal_pos_iff.1 hKf
  obtain ⟨a', ha, hinf, hfin⟩ := hSplit X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ D.R.rS (frameOf X u')
    X.measG (X.measW u') hT1 νH (X.B.I.L : Set _) hStd hLat hdet hn2 hSW1 hSW2 X.measG_norm (X.measW_norm u')
    hOmT hCT (by exact hK0) (by exact hKtop)
  have hR0 := hRB X hb FdN FdN' u u' ψ hHyp hMC hStd.2.2.2 hT1 a' ha hinf
  have e1 : Formalism.L2.SG.Pf.NcReal.eDF D.R.k D.R.rS =
      -(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3 := by
    unfold Formalism.L2.SG.Pf.NcReal.eDF; ring
  rw [e1] at hR0
  have hR : Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' =
      a' * 2 ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F)) *
        (Real.pi ^ D.R.k / (Nat.factorial (D.R.k - 1) : ℝ)) ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) *
        ((Tw u : ℕ) : ℝ) ^ (-((D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F) : ℕ) : ℤ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^
          (-(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3) := hR0
  have hμK : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK =
      (X.measG.μGf (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _))).toReal := by
    show (X.measG.μGf (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _))).toReal /
        (∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _) p.1)).toReal) *
        ∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _) p.1)).toReal = _
    rw [div_mul_cancel₀ _ hprod.ne']
  have hS : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK * a' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' *
        ∏' v : PlX X,
          (omAt X.B.I.cm.sig X.B.I.J ψ v
            ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
            {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
              Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal := by
    rw [hμK]
    exact hfin
  exact Formalism.L2.SG.Pf.NcLeaves.ncTieC_of_leaves X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq a' ha
    hP hM hMs hL hO hTy hV hVG hStd.2.2.1 hStd.2.2.2 hcong hRR hS hR hVo hVt hIx hOm hFD hPC

set_option maxHeartbeats 4000000 in
variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncTie0All_of (hRB : Formalism.L2.SG.Pf.NcReal.RealBracket) (hSW : PI.VolStabS.MassDataS.SWXS)
    (hHyp : HypX X hb FdN FdN' u u') (hMC : MeasCompatψ X ψ) (hStd : StdHyp X.B.I.cm.sig X.B.I.J ψ)
    (hLat : ∃ L : Submodule (NumberField.RingOfIntegers X.B.I.E) (Fin X.B.I.n → X.B.I.E),
      Submodule.IsLattice X.B.I.E L ∧ (L : Set (Fin X.B.I.n → X.B.I.E)) = (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    (hdet' : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0)
    (hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0) (hPC : ProdConv X u u' ψ)
    (hL : LocTieX X ψ u) (hL' : LocTieX X ψ u') (hTF : TypFacts X u u')
    (hQ : Formalism.L2.SG.Pf.MassDataPos.QuotVolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hsd : 0 ≤ sd) (hC0 : 0 ≤ C) (hTh : 0 < Th)
    (hcong : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hRR : IsRowReps D F0 what₂) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) :=
  ncTieAllS_of X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq
    (Formalism.L2.SG.Pf.NcS.SplitPf.splitOm_of_intWitt Formalism.L2.SG.Pf.NcS.IntWittPf.integral_witt_almost_everywhere) hRB hHyp hMC hStd hLat
    hdet' (hSW X).1 (hSW X).2
    (Formalism.L2.SG.Pf.MassDataX.pos_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hSW hHyp hPC hStd.2.2.1 hMC
      hdet hQ hsd hC0 hTh)
    (Formalism.L2.SG.Pf.MassDataX.inMass_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (Formalism.L2.SG.Pf.MassDataX.inMasses_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hHyp)
    (Formalism.L2.SG.Pf.MassDataX.inLevelS_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hHyp)
    (Formalism.L2.SG.MassDataConc.inOrdinary_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hPC)
    (Formalism.L2.SG.Pf.MassDataX.inTyped_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hHyp hPC hL hL' hTF
      hStd.2.2.1 hStd.2.2.2)
    (Formalism.L2.SG.Pf.MassDataX.inVolumes_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hSW hHyp hStd.2.2.1
      hStd.2.2.2 hMC hdet)
    (Formalism.L2.SG.Pf.MassDataX.volHa'_eq X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hSW hStd.2.2.1 hMC)
    hcong hRR (Formalism.L2.SG.Pf.NcVal.volOrdV_holds X u u' ψ) (Formalism.L2.SG.Pf.NcVal.volTypV_holds X u u' ψ)
    (Formalism.L2.SG.Pf.AlTieIdx.indexTypC_holds X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ.omV_holdsX X u' ψ) (Formalism.L2.SG.Pf.AlTieLG.fieldDict_holds X u u') hPC

end Formalism.L2.SG.Pf.NcAllS
