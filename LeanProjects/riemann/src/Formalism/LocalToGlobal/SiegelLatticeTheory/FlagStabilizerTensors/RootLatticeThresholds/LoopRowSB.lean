import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopRowSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBGenIdx

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsFinal Formalism.FourierDecayAlt
  Formalism.L2.SG.ThmSOwn

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BM

variable (C0 : ℝ) {𝒞 : FamClass} (sel : SSel 𝒞) (yF : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → ℝ)

def YtR (hyF : YFOK sel yF) (C1f : List ℝ → ℝ)
    (B : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (_ : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' (C1f Fm.cOut))
    (M : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut) (B Fm hc x hx i u u'))
    {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (x : ℝ) (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
    (u u' : (Fm.D x i).what₂.Word) :
    LoopTie (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut) :=
  loopTieOfParts
    (loopRowsOf (wOf ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X)
      (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1)
      (hOf _ _ _ _) (aOfW _ _ _ _ (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
      (hvOfW _ _ _ _ (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
      (Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds (Fm.D x i)) u u'
      (frameEqvInj_of _ _ (hOf _ _ _ _) (aOfW _ _ _ _ (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
        (hvOfW _ _ _ _ (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
        (Formalism.L2.SG.Pf.LoopBFrame.frameChangeC_holds _ _ _ _ _ _) u u'))
    (B Fm hc x hx i u u') (M Fm hc x hx i u u')

theorem tiesAt {D : D7} (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF))
    (hWD : Formalism.L2.SG.WuDecay.WuDecay X) (u u' : D.what₂.Word) :
    Formalism.MainNotions.BridgeLemma₂.wordPairNormRelation (atOfW X Y hF hI hWD) u u' ∧ @Formalism.MainNotions.BridgeLemma.LatticeDeterminantFactorization D (atOfW X Y hF hI hWD) u u' ∧
      Formalism.MainNotions.BridgeLemma₂.wordPairEntriesInLattice (atOfW X Y hF hI hWD) u u' :=
  ⟨normTieC_holds D X Y hF hI (wOf X) (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD) u u',
    Formalism.L2.SG.Pf.LoopBGenIdx.gram_determinant_relation D X Y hF hI (wOf X) (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD) u u',
    entryLatC_holds D X Y hF hI (wOf X) (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD) u u'⟩

theorem tiesR (hyF : YFOK sel yF) (C1f : List ℝ → ℝ)
    (B : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (_ : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' (C1f Fm.cOut))
    (M : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut) (B Fm hc x hx i u u'))
    {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) :
    Formalism.MainNotions.BridgeLemma₂.rows_TiesF (Fm.raise (yR sel yF Fm hc)) (C1f Fm.cOut) (AtR sel yF hyF Fm hc)
              (YtR sel yF hyF C1f B M Fm hc) ∧
      ∀ x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
        Formalism.MainNotions.BridgeLemma₂.wordPairTermInjective (AtR sel yF hyF Fm hc x hx i) (YtR sel yF hyF C1f B M Fm hc x hx i u u') := by
  have hTI : ∀ x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
      Formalism.MainNotions.BridgeLemma₂.wordPairTermInjective (AtR sel yF hyF Fm hc x hx i) (YtR sel yF hyF C1f B M Fm hc x hx i u u') :=
    fun x hx i u u' t t' hL hE => frameEqvInj_of (wOf ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X) (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hOf ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1))
      (aOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
      (hvOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
      (Formalism.L2.SG.Pf.LoopBFrame.frameChangeC_holds _ _ _ (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) _) u u' t t' hL hE
  refine ⟨Formalism.MainNotions.BridgeLemma₂.family_gram_facts_of_hypotheses _ _ _ _ fun x hx i u u' =>
    ⟨(tiesAt ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2 u u').1,
      (tiesAt ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2 u u').2.1,
      (tiesAt ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2 u u').2.2, hTI x hx i u u'⟩, hTI⟩

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem loopRowS_of_BM (hyF : YFOK sel yF) (C1f : List ℝ → ℝ) (Uf : (List ℝ → ℝ) → List ℝ → Formalism.L2.SG.RowsU.UC)
    (B : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (_ : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' (C1f Fm.cOut))
    (M : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut) (B Fm hc x hx i u u'))
    (hAdmR : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm,
      VanishingOnXAndXPlus.AdmF (Fm.raise (yR sel yF Fm hc)) (C1f Fm.cOut) (AtR sel yF hyF Fm hc) (YtR sel yF hyF C1f B M Fm hc))
    (hUR : ∀ aF : List ℝ → ℝ, Closed 𝒞 fun Fm CH => ∀ hc : 𝒞 Fm,
      Formalism.L2.SG.RowsU.UAdm (Fm.raise (yR sel yF Fm hc)) (C1f Fm.cOut) (AtR sel yF hyF Fm hc) (YtR sel yF hyF C1f B M Fm hc)
        (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (aF Fm.cOut) (Uf aF (Fm.cOut ++ Fm.cMid CH)))
    (hForm : Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      Hyp0 (Fm.D x i) (Fm.L x i) C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) :
    LoopRowS C0 𝒞 sel :=
  loopRowS_of_U C0 sel yF hyF C1f Uf (YtR sel yF hyF C1f B M) hAdmR hUR
    ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ hc => tiesR sel yF hyF C1f B M Fm hc⟩⟩
    hForm

theorem admissible_raise {eps : ℝ} {Fm : FamP eps} {C1 : ℝ} (y : ℝ) (h : AdmRec Fm C1) : AdmRec (Fm.raise y) C1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, h⟩ := h
  exact ⟨a1, a2, fun x hx i => a3 x (raise_lt hx) i, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
    fun x hx => a15 x (raise_lt hx), a16, h⟩

theorem admissible_family_raise {eps : ℝ} {Fm : FamP eps} {C1 : ℝ} (y : ℝ)
    (At : ∀ x, (Fm.raise y).x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
    (Yt : ∀ x (hx : (Fm.raise y).x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
      LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)
    (h : AdmRec Fm C1) (hV : ∀ Cg cb Cu cT CT C0 A : ℝ, VanishingOnXAndXPlus.FamilyTermVolumeSmallCellBound (Fm.raise y) C1 At Yt Cg cb Cu cT CT C0 A) :
    VanishingOnXAndXPlus.AdmF (Fm.raise y) C1 At Yt :=
  family_admitted_of_parts (Fm.raise y) C1 At Yt (admissible_raise y h) hV

end BM

end Formalism.L2.SG.LoopsTies
