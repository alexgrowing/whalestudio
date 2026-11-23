import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.MahlerFinal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.CutCountOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumProdEqPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLogSizeM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFundamentalDomainRangeProdMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMulSqLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulLeSqAddSq

namespace PositivityTheory.Rg.BcB.E1

open D1

theorem sizeCont : SizeCont := GlobalTheory.CompanionTheory.SizeCont.sizeCont szFin
theorem degRight : DegRight := GlobalTheory.CompanionTheory.DegRightProof.degRight_of mulF mulI szFin finSupp
theorem redBasic : RedBasic := redBasic_of ratProper_holds sizeCont
theorem cutBox : CutBox := cutBox_of' degBasis degAdelic degBdd
theorem redCell : RedCell := redCell_of sizeBasic degBdd degRat degRight torNorm_holds cutBox redBasic
theorem cutRed : CutRed := cutRed_of degRat cellCover_holds cutBox redBasic redCell
theorem cntPair : CntPair := cntPair_of ratProper_holds thetaBasic_holds
theorem wtCount : WtCount := wtCount_of ratProper_holds cellSum cellCover_holds redBasic redCell GlobalTheory.CompanionTheory.LatticeSum.latSum
theorem cutCount : CutCount := cutCount_of redBasic cutRed wtCount
theorem wtDiag : WtDiag := wtDiag_of ratProper_holds cntBasic wtCount
theorem vecsEx : VecsEx := GlobalTheory.CompanionTheory.DualVectorFamily.vecsEx_of ratProper_holds kerBasic kerLin cntBasic cntPair vecEx vecNorm vecInner ptEq
theorem lBound : LBound := GlobalTheory.CompanionTheory.LBoundProof.lBound_of mahler_holds cutCount
theorem sFun_holds : SFun := sFun_of vecsEx lBound
theorem sBound_holds : F.SBound := sBound_of (sb_of sFun_holds)
theorem bridge_holds : F.Bridge := bridge_of (GlobalTheory.CompanionTheory.PairDom.prodDom ratProper_holds)
theorem opEx_holds : F.OpEx := opEx_of ratProper_holds opExA opAdj opMul
theorem kernel_operator_exists_holds : E.SmoothSeminormGrowth := kernel_operator_exists_of opEx_holds
theorem kernel_diagonal_integrable_holds : E.KernelDiagonalIntegrable := kernel_diagonal_integrable_of ratProper_holds kerBasic kerLin opEx_holds wtDiag
theorem growthJ_of_ell (h : D4.EllFormula2J) : GrowthJ := growthJ_of h sBound_holds bridge_holds domEx_holds

open MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL in
theorem nonempty_dom (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (a b : ℕ) : Nonempty (PositivityTheory.Rg.BcB.E.Dom E a b) := by
  obtain ⟨F₁, h₁⟩ := domEx_holds E a Measure.haar
  obtain ⟨F₂, h₂⟩ := domEx_holds E b Measure.haar
  obtain ⟨D, -⟩ := bridge_holds E a b Measure.haar Measure.haar F₁ F₂ h₁ h₂
  exact ⟨D⟩

end PositivityTheory.Rg.BcB.E1
