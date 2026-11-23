import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClass
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqAna
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqPoints
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNormOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNormals
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormChainLemmas
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormHSBlocks
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormChiNBi
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormExpSatHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqVanish

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut
  Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqClass Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf

theorem stepThmBPinnedG_of_bdat (h : Formalism.L2.SG.Pf.BDat.StepThmBG) : StepThmBPinnedG := h

theorem liftIotaEqC_of (h : Formalism.L2.SG.Pf.IotaDictC) : LiftIotaEqC := by
  intro D X Y u _ s₁ s₂ h1 h2 h3 h4 h5
  have h' := h D X Y u u s₁ s₂ h1 h2 h3 h4
  first
  | unfold Full.tO at h5
  | unfold Formalism.L2.SG.Full.Full.tO at h5
  | unfold Formalism.L2.SG.Full.tO at h5
  | simp only [Full.tO] at h5
  | dsimp only at h5
  first
  | unfold tOf at h5
  | simp only [tOf] at h5
  | unfold Formalism.L2.SG.TermOp.tOf at h5
  dsimp only at h5
  first
  | unfold rowOf at h5
  | simp only [rowOf] at h5
  | unfold Formalism.L2.SG.TermOp.rowOf at h5
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h5
  exact (h' h5.1 h5.2.1).1 h5.2.2

theorem rowMainEqC_of_leaves (hI : Formalism.L2.SG.Pf.IotaDictC) (hNI : Formalism.L2.SG.NGCut.NormalInvariants.Gen.NmlInvG)
    (hNC : Formalism.L2.SG.NGCut.NormalInvariants.NormCount)
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w)
    (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : Formalism.L2.SG.Pf.MainEqVanish.FormGC)
    (hL : StepLocGenPinnedG) (hT : Formalism.L2.SG.Pf.BDat.StepThmBG) : RowMainEqC :=
  rowMainEqC_of_pinned Formalism.FourierDecayAlt.P.norm_chain (stepClassG_of_liftIota (liftIotaEqC_of hI))
    (Formalism.L2.SG.NGCut.NormalInvariants.Gen.stepNormalsG_of hNI hNC (Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen.stepNormOneG_of hOV hAt))
    (Formalism.L2.SG.Pf.MainEqPoints.stepPointsG_of hOV hAt) (Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen.stepNormOneG_of hOV hAt)
    hTi hB hE (Formalism.L2.SG.Pf.MainEqVanish.stepTermVanishG_of_form hV) hL (stepThmBPinnedG_of_bdat hT)

theorem normExpDegC_of_leaves (hFL : Formalism.L2.SG.Pf.FinLeviC) (hOL : Formalism.L2.SG.Pf.OOLintSumC) : NormExpDegC :=
  normExpDegC_of hilbert_schmidt_blocks (Formalism.L2.SG.Closed.FoldOKC_holds hFL) (Formalism.L2.SG.Closed.OOIntAllC_holds hOL)
    (Formalism.L2.SG.Closed.AbsConvC_holds hOL) Formalism.L2.SG.Closed.AmpWellDefC_holds Formalism.L2.SG.Closed.OOFundIndepC_holds
    (fun _ X => chi_n_bilinear X) (fun D X Y u _ => Formalism.L2.SG.NormCut.colFreeAll D X Y u)
    (fun D X Y u _ h1 h2 h3 =>
      Formalism.L2.SG.NormCut.degLeftAct_of_PD (fun D => Formalism.L2.SG.Pf.positive_definite_isomorphism D) D X Y u h1 h2 h3)
    (fun D X Y u _ h1 h2 h3 => Formalism.L2.SG.NormCut.degRightAct_holds D X Y u h1 h2 h3)

end Formalism.L2.SG.Pf
