import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSClosedP
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.VolumeNormalizedOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowsInputPOfTermsFiniteSig
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowsSumCPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NGLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataClose
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DensLoc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocFramePrim
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PointUniformity
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModelKSD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXVolAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NuQPinExistsHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowFormAllOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepPinExistsOfPlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensAtD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXTyped
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealObjInInfinityXOfG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootPatterns
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlInvHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefCutDeep
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXSIdx
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaCTHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpValAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MassDataPosAllOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXDens
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DvPosC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvHoldsGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyJSZ
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.VolumeDeterminedOfChart
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NormalizingConstantPositiveAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.RealBracketOfRowBlock
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CutLeavesDeepOutright
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXPinsP
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXVIndepP
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KFinDensePf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFF

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.L2.SG.SpectralTiesReal Formalism.L2.SG.PoincareAmplitudeLowerBounds

namespace Formalism.L2.SG.TheoremSConclusion

def TheoremSClosedHypotheses : Prop :=
  (∀ D : D7, Formalism.L2.SG.DataInst.LocalModelAt D) ∧ (∀ D : D7, Formalism.L2.SG.Pf.LocCP.LocTied D → Formalism.L2.SG.DataInst.DensInputAt D) ∧
  (∀ D : D7, Formalism.L2.SG.SpectralTiesReal.RowsInputP D) ∧ Formalism.L2.SG.RowsPos.RowNGP ∧ Formalism.L2.SG.RowsConc.KppOffC ∧ CarrierP ∧
  KernelExponentAgreement ∧ Formalism.L2.SG.Full.FoldOKC ∧ Formalism.L2.SG.Full.OOIntAllC ∧ Formalism.L2.SG.Full.AbsConvC ∧ FinXC ∧
  Formalism.L2.SG.Pf.WuDecayOfGap ∧ ChoicesC ∧ FormulaC ∧ RowsSumC ∧ RowFormAllP ∧ MassDataHypAll ∧ LinkAll ∧ SplitAll

theorem rowsInputP_of_dataCut {D : D7} (h : Formalism.L2.SG.DataCut.RowsInputP D) : Formalism.L2.SG.SpectralTiesReal.RowsInputP D :=
  fun Wp Wq _ _ _ _ S δ M hA L u u' hT hC hPH F0 what₂ hR ϖ hϖ nc hF α hα hB =>
    h Wp Wq S δ M hA L u u' hT hPH hC F0 what₂ hR ϖ hϖ nc hF α hα hB

theorem theoremS_of_conj (h : TheoremSClosedHypotheses) (Cthr : ℝ) :
    ∃ C₄ CA C : ℝ, 1 ≤ C₄ ∧ Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, 0 < cb → 0 < cTf → ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word), Formalism.BasicNotions.Ties D → u ≠ u' → 0 ≤ L.sc.b →
      SizesAt CA C0 CG CDel cT Cb Cn k0 D L T u u' →
      Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f → Formalism.MainNotions.S.Cnt.Stand D u u' →
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D L C' Cl Cg cb Cw cTf CT C0f →
      Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D → Formalism.L2.SG.RowsConc.TFrameAt D →
      (T.Y.tO u u').RowBig (Formalism.L2.SG.RowsConc.epsL D) (Formalism.L2.SG.RowsConc.ddC T.X T.Y u u') →
      (T.Y.tO u u').RowNotScalar (Formalism.L2.SG.RowsConc.epsL D) (Formalism.L2.SG.RowsConc.ddC T.X T.Y u u') →
      ‖(T.Y.tO u u').K0‖ ^ 2 ≤ (1 + (L.sc.b ^ 6)⁻¹) * ((D.duS u : ℝ) * (D.duS u') / D.what₂.Dstar) ∧
      L.hsSq u u' ≤ (1 + L.sc.b ^ (-(6 : ℝ))) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  exact theoremS_closedP h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 Cthr

theorem kExpTiedS_holds : KernelExponentAgreement := by
  intro D X Y u u' hT
  have f1 := Formalism.L2.SG.Closed.FoldOKC_outright D X Y u hT.1 hT.2.2.2.2.1
  have f2 := Formalism.L2.SG.Closed.FoldOKC_outright D X Y u' hT.1 hT.2.2.2.2.1
  have hFE := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u'
  have hOO := Formalism.L2.SG.Closed.OOIntAllC_outright D X Y u u' f1 f2 hFE
  exact Formalism.L2.SG.Closed.KExpansionC_holds D X Y u u' f1 f2
    (Formalism.L2.SG.Closed.InHHC_holds D X Y u hT.2.2.2.2.2.1 f1) (Formalism.L2.SG.Closed.InHHC_holds D X Y u' hT.2.2.2.2.2.1 f2) hFE hOO
    (Formalism.L2.SG.Closed.OOFundIndepC_holds D X Y u u' hFE hOO) (Formalism.L2.SG.Closed.AmpWellDefC_holds D X Y u u' hOO)
    (Formalism.L2.SG.Closed.AbsConvC_outright D X Y u u' f1 f2 hFE hOO)

end Formalism.L2.SG.TheoremSConclusion
