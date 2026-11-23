import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenFirstParametersOfPrintsUEStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Prm1
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HermWCellLastMulMulVecEqOfInWbStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEDcPtLinkedStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinLinkedRealizationStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTheoremPublishedInputsThird
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtHDivGOfMiStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealGroupInputsCombined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HarishChandraInputsCombined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedBundlesGoodOfLocalLanglands
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLabOfLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGeo0AtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointEvaluationSideStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.S0.Open0ProofU
theorem open_orbit_of_unramified_exponents_alt : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ), _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) := by
  intro P hL cDep
  have hNE : ∀ K B f T w Z Wt p0 t nch n xd c, _root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep K B f T w Z Wt p0 t nch n xd c →
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c) := fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1⟩
  have hB : ∀ (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep).s K), GlobalTheory.Mem.R3.Rw.BkLaw (q.w.D q.Z) := fun _ q => q.x.nx.2.1.2.down
  have hPA := _root_.GlobalTheory.T.linkedAt_hPA_prmR hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hDc := _root_.GlobalTheory.T.linkedAt_hDcPtG_prmR hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hTie := _root_.GlobalTheory.T.linkedAt_tie_of_nonempty_extensionWithLaw P.discreteSeriesCover P.harishChandraModules P.casselmanWallach P.weilRepresentationUnitaryPair
    P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay hL _ SExt.none (geoCl anyGeometry) hNE
  have hJ := _root_.GlobalTheory.T.entries_combined_real_alt P.weilRepresentationUnitaryPair P.discreteSeriesExists P.discreteSeriesCover P.harishChandraModules
    P.casselmanWallach P.harishChandraFinite P.cuspRapidDecay hL _ SExt.none (geoCl anyGeometry) hPA hDc hTie
  have hMi := _root_.GlobalTheory.T.main_theorem_published_inputs_third_alt_alt P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover P.harishChandraModules P.casselmanWallach
    GlobalTheory.Hk3.howeUnram_holds P.weilRepresentationUnitaryPair P.weilSiegelFormulaUnitary P.siegelWeilUnitaryConvergent
    P.doublingMethod P.unramifiedDoublingGL P.discreteSeriesClassification P.strongApproxSU P.siegelWeilUnitaryConvergent2
    hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hDiv := _root_.GlobalTheory.T.bk_law_entries_alt P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    P.discreteSeriesCover P.harishChandraModules P.casselmanWallach hL _ SExt.none (geoCl anyGeometry) hB hMi.1
  have hLam := _root_.GlobalTheory.T.real_group_inputs_combined_alt_alt P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    P.harishChandraAnalyticity P.discreteSeriesClassification P.cuspTraceClass P.dixmierMalliavinFactorisation
    P.flathFactorisation
    P.zelevinskyPolynomialRing P.geometricLemma P.greenCuspidal hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  have hKap := _root_.GlobalTheory.T.harish_chandra_inputs_combined_alt_alt P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover P.harishChandraModules
    P.casselmanWallach P.harishChandraAnalyticity P.discreteSeriesClassification P.cuspTraceClass
    P.dixmierMalliavinFactorisation P.flathFactorisation P.zelevinskyPolynomialRing P.geometricLemma P.greenCuspidal
    hL _ SExt.none (geoCl anyGeometry) hLam
  have hGood := _root_.GlobalTheory.T.linked_bundles_good_of_local_langlands_alt_alt (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) P.zelevinskyPolynomialRing hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry) hNE
  have hLab := _root_.GlobalTheory.T.good_ft_entries_alt_alt (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) P.zelevinskyPolynomialRing hL _ SExt.none (geoCl anyGeometry) hNE hGood.1
  have hGeo := _root_.GlobalTheory.T.linkedAt_geometricWeakTies_of_tie P.rayClassFieldSt hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry) hNE hDiv hTie
  have hDf := _root_.GlobalTheory.T.weil_unitary_entries' P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
  exact ⟨hPA, hLam, hDiv, hDc, hJ, hTie, hLab, hGood.2, hGeo, hMi.2, hKap, hDf⟩
end GlobalTheory.Fc.S0.Open0ProofU
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open0_of_unitary_group_hypotheses : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ), _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) := by
  first | exact @_root_.GlobalTheory.Fc.S0.Open0ProofU.open_orbit_of_unramified_exponents_alt | exact _root_.GlobalTheory.Fc.S0.Open0ProofU.open_orbit_of_unramified_exponents_alt | (intros; apply _root_.GlobalTheory.Fc.S0.Open0ProofU.open_orbit_of_unramified_exponents_alt <;> assumption)
end
end
