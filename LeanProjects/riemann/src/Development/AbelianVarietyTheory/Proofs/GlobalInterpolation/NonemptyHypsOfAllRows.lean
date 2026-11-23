import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Development.AutomorphicArithmetic.CharacterBoxes.ClassSel
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WorkingClassesFrozen
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WorkingFamClassCopiesEqFrozenStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GenusMassEntryStatement
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc

theorem nonempty_hyps_of_allRows : StandardLattice.SiegelMassRatioCM → LitThin → Formalism.L2.SG.Pf.WuDecayOfGap → Formalism.L2.SG.RowsDef.RowsFinDim → Formalism.L2.SG.RowsPos.TypeP → Formalism.L2.SG.RowsPos.RowNGP → Formalism.L2.SG.RowsPos.RowMainEqP → (∀ D, MassRatioUnderVolume D) → (∀ D, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassAt D 2) → ∀ (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT Bundle) (N : FamClass → Prop) (DR : R1.DefT), (DC.MinkDiv → GroupRetwisting.BaseCond KP ∧ GroupRetwisting.FirstG KP Q ∧ GroupRetwisting.ExportF KP Q ∧ GroupRetwisting.SecondG KP Q Q') → ExBL KP Q Q' Lk → AllRows KP Q Q' Lk N DR → Nonempty (Hyps N DR) := by
  intro hP hLit hWu hRF hTy hNG hM hU hG KP Q Q' Lk N DR hc hx hA
  obtain ⟨R30, hR30, c30, cIc, hb30, hpos, r30⟩ := hA.c30
  have rTu := Row.rowL (KP := KP) (Q := Q) largeBaseProperty_true (GlobalTheory.T.genus_mass_entry hU hG Q' Lk)
  have hall := RowL.and (hA.hn4 : RowL KP Q Q' Lk fun 𝒜 _ => R0.ClassCountBoundAllPoints 𝒜) <|
    RowL.and (hA.jOn : RowL KP Q Q' Lk fun 𝒜 _ => R0.H_jOn 𝒜) <|
    RowL.and (hA.hInstR : RowL KP Q Q' Lk fun 𝒜 _ => ClassTwoEntries.H_hInstR 𝒜) <|
    RowL.and (hA.aC2 : RowL KP Q Q' Lk fun 𝒜 _ => ClassTwoEntries.DivisionSecondComplementAdmissible 𝒜) <|
    RowL.and (hA.aP10 : RowL KP Q Q' Lk fun 𝒜 _ => AllBundlePointProperties.LevelPrimeColumnValuationsClosed 𝒜) <|
    RowL.and (hA.aAtG : RowL KP Q Q' Lk fun 𝒜 _ => AllBundlePointProperties.H_aAtG 𝒜) <|
    RowL.and (hA.aPt0 : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.ReferenceChainEvaluationAdmissible 𝒜) <|
    RowL.and (hA.aPtTw : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_aPtTw 𝒜) <|
    RowL.and (hA.aPer0 : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_aPer0 𝒜) <|
    RowL.and (hA.aPerTw : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_aPerTw 𝒜) <|
    RowL.and (hA.tie : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_tie 𝒜) <|
    RowL.and (hA.hRB : RowL KP Q Q' Lk (AtAll R1.P_hRB)) <|
    RowL.and (hA.hTw : RowL KP Q Q' Lk (AtAll R1.P_hTw)) <|
    RowL.and (hA.hPA : RowL KP Q Q' Lk (AtAll R1.P_hPA)) <|
    RowL.and (hA.hLamP : RowL KP Q Q' Lk (AtAll R1.P_hLamP)) <|
    RowL.and (hA.hDivG : RowL KP Q Q' Lk (AtAll R1.P_hDivG)) <|
    RowL.and (hA.hDcPtG : RowL KP Q Q' Lk (AtAll R1.P_hDcPtG)) <|
    RowL.and (hA.selJ : RowL KP Q Q' Lk (AtAll R1.P_selJ)) <|
    RowL.and (hA.sLp : RowL KP Q Q' Lk R1.H_sLp) <|
    RowL.and (hA.sO : RowL KP Q Q' Lk R1.H_sO) <|
    RowL.and (hA.hServ : RowL KP Q Q' Lk R1.H_hServ) <|
    RowL.and (hA.zL : RowL KP Q Q' Lk R1.H_zL) <|
    RowL.and (hA.hTF : RowL KP Q Q' Lk fun 𝒜 _ => R1.H_hTF 𝒜) <|
    RowL.and (hA.rRows : RowL KP Q Q' Lk (R1.H_rRows DR)) <|
    RowL.and (hA.nRest : RowL KP Q Q' Lk fun 𝒜 _ => N (GlobalTheory.Cp.D3 3 𝒜)) <|
    RowL.and (⟨R30, hR30, r30⟩ : RowL KP Q Q' Lk _) rTu
  obtain ⟨𝒜, σ, hE, hD, -, hn4, jOn, hInstR, aC2, aP10, aAtG, aPt0, aPtTw, aPer0, aPerTw, tie, hRB, hTw, hPA, hLamP, hDivG,
    hDcPtG, selJ, sLp, sO, hServ, zL, hTF, rRows, nRest, ⟨h30, irrC⟩, hTu⟩ :=
    UpperTheory.Top.classSel hP (fun D => hU D) KP Q Q' Bundle Lk _ (fun _ y => Formalism.MainNotions.StandardLattice.HarishChandraReduction.cTmin y) hc hx hall
  have s3 : ∀ {eps : ℝ} (Fm : FamP eps), GlobalTheory.Cp.D3 3 𝒜 Fm → W3 𝒜 Fm := fun Fm h => ((GlobalTheory.T.workingFamClass_copies_eq_frozen.1 𝒜 _ Fm).1).1 h
  have s1 : ∀ {eps : ℝ} (Fm : FamP eps), Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (GlobalTheory.Cp.WithChN 𝒜)) Fm → W1 𝒜 Fm :=
    fun Fm h => ((GlobalTheory.T.workingFamClass_copies_eq_frozen.1 𝒜 _ Fm).2).1 h
  exact ⟨{
    𝒜 := 𝒜
    σ := σ
    cT := fun _ y => Formalism.MainNotions.StandardLattice.HarishChandraReduction.cTmin y
    hEx := fun hM la G hla hH => working_classes_frozen.2 _ _ (fun hM' => hE hM' la G hla hH) hM
    hduty := fun Fm h => GlobalTheory.T.workingFamClass_copies_eq_frozen.2 _ Fm (hD _ Fm h).1
    hRB := fun Fm hc x hx _ i => hRB Fm hc x hx i
    hTw := fun Fm hc x hx _ i => hTw Fm hc x hx i
    hPA := fun Fm hc x hx _ i => hPA Fm hc x hx i
    hLamP := fun Fm hc x hx _ i => hLamP Fm hc x hx i
    hDivG := fun Fm hc x hx _ i => hDivG Fm hc x hx i
    hDcPtG := fun Fm hc x hx _ i => hDcPtG Fm hc x hx i
    hTu := hTu
    hn4 := Formalism.MainNotions.Pk.Closed.sub hn4 s1
    hLit := hLit
    hWu := hWu
    hRF := hRF
    hTF := hTF
    c30 := c30
    hc30 := hb30
    sTy := hTy
    sNG := hNG
    sM := hM
    sLp := sLp
    sO := sO
    h30 := h30
    hInstR := fun Fm hc x hx _ i => hInstR Fm hc x hx i
    selJ := fun Fm hc x hx _ i => Classical.choice (selJ Fm hc x hx i)
    jOn := Formalism.MainNotions.Pk.Closed.sub jOn s3
    hMt := fun Fm h => (hD _ Fm h).2
    rRows := rRows
    aPt0 := Formalism.MainNotions.Pk.Closed.sub aPt0 s3
    aPtTw := Formalism.MainNotions.Pk.Closed.sub aPtTw s3
    aPer0 := Formalism.MainNotions.Pk.Closed.sub aPer0 s3
    aPerTw := Formalism.MainNotions.Pk.Closed.sub aPerTw s3
    aP10 := Formalism.MainNotions.Pk.Closed.sub aP10 s3
    aAtG := Formalism.MainNotions.Pk.Closed.sub aAtG s3
    aC2 := Formalism.MainNotions.Pk.Closed.sub aC2 s3
    hServ := hServ
    cIc := cIc
    hcI := hpos
    irrC := irrC
    zL := zL
    tie := Formalism.MainNotions.Pk.Closed.sub tie s3
    hU := hU
    hG := hG
    nRest := nRest }⟩

end GlobalTheory.Fc
